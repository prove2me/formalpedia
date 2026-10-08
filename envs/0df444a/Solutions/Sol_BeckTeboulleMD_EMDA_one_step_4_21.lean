-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.one_step_4_21
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:58:15.866914+00:00
-- url     : https://prove2.me/submissions/e4d6e0b7-99ab-4426-990b-72b1dfb22865

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

set_option autoImplicit false

open Filter Topology in
theorem pd0fe_sc_key {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (σ : ℝ) (hψ : StrongConvexOn X σ ψ)
    (u : E) (hu : u ∈ X) (y : E) (hy : y ∈ X) (hd : DifferentiableAt ℝ ψ y) :
    fderiv ℝ ψ y (u - y) ≤ ψ u - ψ y - σ / 2 * ‖u - y‖ ^ 2 := by
  set v := u - y with hv
  set g : ℝ → ℝ := fun t => ψ (y + t • v) with hg
  have hline : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
  have hgd : HasDerivAt g (fderiv ℝ ψ y v) 0 := by
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ y) (y + (0:ℝ) • v) := by
      simpa using hd.hasFDerivAt
    exact h1.comp_hasDerivAt (0:ℝ) hline
  have hslope := hgd.tendsto_slope_zero_right
  have hbound : ∀ᶠ t in 𝓝[>] (0:ℝ),
      t⁻¹ • (g (0 + t) - g 0) ≤ ψ u - ψ y - (1 - t) * (σ / 2 * ‖v‖ ^ 2) := by
    have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have key := hψ.2 hu hy (le_of_lt ht0) (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
    have hpt : t • u + (1 - t) • y = y + t • v := by
      rw [hv, smul_sub, sub_smul, one_smul]; abel
    rw [hpt] at key
    simp only [smul_eq_mul] at key
    have hg0 : g 0 = ψ y := by simp [hg]
    have hgt : g (0 + t) = ψ (y + t • v) := by simp [hg]
    rw [hg0, hgt, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht0]
    have : ‖u - y‖ = ‖v‖ := rfl
    rw [this] at key
    nlinarith [key]
  have hlim : Tendsto (fun t : ℝ => ψ u - ψ y - (1 - t) * (σ / 2 * ‖v‖ ^ 2))
      (𝓝[>] (0:ℝ)) (𝓝 (ψ u - ψ y - (1 - 0) * (σ / 2 * ‖v‖ ^ 2))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((continuous_const.sub ((continuous_const.sub continuous_id).mul
      continuous_const))).tendsto 0 |>.congr (fun _ => rfl)
  have := le_of_tendsto_of_tendsto hslope hlim hbound
  simpa using this

open BeckTeboulleMD.EMDA in
theorem pd0fe_opt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (ψ : E → ℝ) (g : E → E →L[ℝ] ℝ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x) :
    ∀ k, 1 ≤ k → ∀ u ∈ X,
      0 ≤ t k * g (x k) (u - x (k + 1)) + fderiv ℝ ψ (x (k + 1)) (u - x (k + 1))
        - fderiv ℝ ψ (x k) (u - x (k + 1)) := by
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
  rw [← this]; exact mul_nonneg htpos.le key'

open BeckTeboulleMD.EMDA in
open BeckTeboulleMD.EMDA in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X)
    (f : E → ℝ) (hf : ConvexOn ℝ X f)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (g : E → E →L[ℝ] ℝ) (hg : ∀ x ∈ X, ∀ y ∈ X, f x + g x (y - x) ≤ f y)
    (ψ : E → ℝ) (σ : ℝ) (hσ : 0 < σ) (hψ : StrongConvexOn X σ ψ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x) :
    ∀ k, 1 ≤ k → t k * (f (x k) - f xstar)
      ≤ bregman ψ xstar (x k) - bregman ψ xstar (x (k + 1))
        + 1 / (2 * σ) * t k ^ 2 * ‖g (x k)‖ ^ 2 := by
  intro k hk
  obtain ⟨htpos, hxk, hdk, _⟩ := hrun k hk
  obtain ⟨_, hxk1, hdk1, _⟩ := hrun (k + 1) (by omega)
  have hopt := pd0fe_opt X hXconv ψ g t x hrun k hk xstar hxstar
  set y := x (k + 1) with hy
  have hsc := pd0fe_sc_key X ψ σ hψ y hxk1 (x k) hxk hdk
  have hgk := hg (x k) hxk xstar hxstar
  set Lf := ‖g (x k)‖ with hLf
  set G := g (x k) with hG
  set Dk := fderiv ℝ ψ (x k) with hDk
  set Dy := fderiv ℝ ψ y with hDy
  have hsplit1 : xstar - x k = (xstar - y) + (y - x k) := by abel
  have hsplit2 : xstar - y = (xstar - x k) + (x k - y) := by abel
  have hD1 : Dk (xstar - x k) = Dk (xstar - y) + Dk (y - x k) := by
    rw [hsplit1, map_add]
  have hG1 : G (xstar - y) = G (xstar - x k) + G (x k - y) := by
    rw [hsplit2, map_add]
  have hGb : G (x k - y) ≤ Lf * ‖x k - y‖ := by
    have h1 := G.le_opNorm (x k - y)
    exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ h1))
  have hnorm : ‖x k - y‖ = ‖y - x k‖ := norm_sub_rev _ _
  set d := ‖y - x k‖ with hd
  have hquad : t k * (Lf * d) ≤ σ / 2 * d ^ 2 + 1 / (2 * σ) * t k ^ 2 * Lf ^ 2 := by
    have h : 0 ≤ (σ * d - t k * Lf) ^ 2 / (2 * σ) := by positivity
    have e : (σ * d - t k * Lf) ^ 2 / (2 * σ)
        = σ / 2 * d ^ 2 + 1 / (2 * σ) * t k ^ 2 * Lf ^ 2 - t k * (Lf * d) := by
      field_simp; ring
    linarith
  unfold bregman
  have hmul : t k * G (x k - y) ≤ t k * (Lf * d) := by
    rw [← hnorm]; exact mul_le_mul_of_nonneg_left hGb htpos.le
  have h1 : t k * (f (x k) - f xstar) ≤ -(t k * G (xstar - x k)) := by
    have := mul_le_mul_of_nonneg_left (show f (x k) - f xstar ≤ -G (xstar - x k) by linarith)
      htpos.le
    linarith
  have h2 : t k * G (xstar - y) = t k * G (xstar - x k) + t k * G (x k - y) := by
    rw [hG1, mul_add]
  linarith [hmul, hquad, hsc, hopt, hD1, h2, h1]
