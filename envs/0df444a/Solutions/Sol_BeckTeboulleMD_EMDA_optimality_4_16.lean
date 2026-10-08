-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.optimality_4_16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:46:52.467065+00:00
-- url     : https://prove2.me/submissions/bd4f1b2a-e4bc-4931-9fa2-ed1175831d3d

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

set_option autoImplicit false

open BeckTeboulleMD.EMDA in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (ψ : E → ℝ) (g : E → E →L[ℝ] ℝ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x) :
    ∀ k, 1 ≤ k → ∀ u ∈ X,
      0 ≤ (t k • g (x k) + fderiv ℝ ψ (x (k + 1)) - fderiv ℝ ψ (x k)) (u - x (k + 1)) := by
  intro k hk u hu
  obtain ⟨htpos, hxk, hdk, hmin⟩ := hrun k hk
  obtain ⟨_, hxk1, hdk1, _⟩ := hrun (k + 1) (by omega)
  set y := x (k + 1) with hy
  set D := fderiv ℝ ψ (x k) with hD
  set c : ℝ := 1 / t k with hc
  let F : E → ℝ := fun v => g (x k) v + c * (ψ v - ψ (x k) - D (v - x k))
  let F' : E →L[ℝ] ℝ := g (x k) + c • (fderiv ℝ ψ y - D)
  have hF : HasFDerivAt F F' y := by
    have h1 : HasFDerivAt (fun v => D (v - x k)) D y := by
      have := D.hasFDerivAt (x := y)
      have h2 : (fun v => D (v - x k)) = fun v => D v - D (x k) := by
        funext v; simp [map_sub]
      rw [h2]; exact this.sub_const _
    have h3 : HasFDerivAt (fun v => ψ v - ψ (x k) - D (v - x k)) (fderiv ℝ ψ y - D) y :=
      (hdk1.hasFDerivAt.sub_const _).sub h1
    exact (g (x k)).hasFDerivAt.add (h3.const_mul c)
  have hminOn : IsMinOn F X y := by
    intro v hv
    have := hmin v hv
    simp only [bregman] at this
    simpa [F, D, c] using this
  have hcone : u - y ∈ posTangentConeAt X y :=
    sub_mem_posTangentConeAt_of_segment_subset (hXconv.segment_subset hxk1 hu)
  have key := (hminOn.localize.on_subset subset_rfl |> fun h => h).hasFDerivWithinAt_nonneg
    hF.hasFDerivWithinAt hcone
  have key' : 0 ≤ g (x k) (u - y) + c * (fderiv ℝ ψ y (u - y) - D (u - y)) := by
    simpa [F'] using key
  have hc' : t k * c = 1 := by rw [hc]; field_simp
  have : t k * (g (x k) (u - y) + c * (fderiv ℝ ψ y (u - y) - D (u - y)))
      = t k * g (x k) (u - y) + fderiv ℝ ψ y (u - y) - D (u - y) := by
    rw [mul_add, ← mul_assoc, hc', one_mul]; ring
  have hfin : 0 ≤ t k * g (x k) (u - y) + fderiv ℝ ψ y (u - y) - D (u - y) := by
    rw [← this]; exact mul_nonneg htpos.le key'
  simpa [smul_eq_mul] using hfin
