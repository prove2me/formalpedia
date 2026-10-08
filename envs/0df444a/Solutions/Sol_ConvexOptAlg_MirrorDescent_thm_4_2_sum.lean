-- Prove2me | solution 1 for ConvexOptAlg.MirrorDescent.thm_4_2_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:38:42.558991+00:00
-- url     : https://prove2.me/submissions/1625f58c-d29b-436f-8c21-1fc87086a08d

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

set_option autoImplicit false

namespace MD8700Aux

open ConvexOptAlg.MirrorDescent

/-- First-order optimality of the Bregman projection. -/
theorem proj_opt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hS : Convex ℝ S) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (y z u : E)
    (hz : z ∈ S) (hu : u ∈ S) (hmin : ∀ w ∈ S, bregman Φ Φ' z y ≤ bregman Φ Φ' w y)
    (hd : HasFDerivAt Φ (Φ' z) z) :
    0 ≤ (Φ' z - Φ' y) (u - z) := by
  have hh : HasFDerivAt (fun w => bregman Φ Φ' w y) (Φ' z - Φ' y) z := by
    unfold bregman
    have h2 : HasFDerivAt (fun w => Φ' y (w - y)) (Φ' y) z := by
      refine (((Φ' y).hasFDerivAt (x := z)).sub_const (Φ' y y)).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall (fun w => by simp [map_sub])
    exact (hd.sub_const (Φ y)).sub h2
  have hmin' : IsMinOn (fun w => bregman Φ Φ' w y) S z := fun w hw => hmin w hw
  have hcone : u - z ∈ posTangentConeAt S z :=
    sub_mem_posTangentConeAt_of_segment_subset (hS.segment_subset hz hu)
  exact hmin'.localize.hasFDerivWithinAt_nonneg hh.hasFDerivWithinAt hcone

end MD8700Aux

open ConvexOptAlg.MirrorDescent in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ)
    (f : E → ℝ) (hf : ConvexOn ℝ X f) (L : ℝ)
    (η : ℝ) (hη : 0 < η) (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hgL : ∀ s : ℕ, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (hrun : IsMirrorDescentRun X D Φ Φ' f η x y g t)
    (u : E) (hu : u ∈ X ∩ D) :
    ∑ s ∈ Finset.Icc 1 t, (f (x s) - f u) ≤
      bregman Φ Φ' u (x 1) / η + η * (L ^ 2 * t / (2 * ρ)) := by
  obtain ⟨_, hXc, ⟨_, hDc, _, hder, _, _⟩, _, _⟩ := hset
  have hS : Convex ℝ (X ∩ D) := hXc.inter hDc
  obtain ⟨hx1, _, hstep⟩ := hrun
  -- membership of iterates
  have hmem : ∀ s, 1 ≤ s → s ≤ t + 1 → x s ∈ X ∩ D := by
    intro s h1 h2
    rcases Nat.lt_or_ge s 2 with h | h
    · have : s = 1 := by omega
      subst this; exact hx1
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      exact (hstep k (by omega) (by omega)).2.2.2.1
  set C : ℝ := η ^ 2 * L ^ 2 / (2 * ρ) with hC
  -- one step
  have hone : ∀ s, 1 ≤ s → s ≤ t →
      η * (f (x s) - f u) ≤ bregman Φ Φ' u (x s) - bregman Φ Φ' u (x (s + 1)) + C := by
    intro s h1 h2
    obtain ⟨hsub, _, hgrad, hproj⟩ := hstep s h1 h2
    have hxs := hmem s h1 (by omega)
    have hz := hmem (s + 1) (by omega) (by omega)
    have hopt := MD8700Aux.proj_opt (X ∩ D) hS Φ Φ' (y (s + 1)) (x (s + 1)) u hz hu hproj.2
      (hder _ hz.2)
    have hsg := hsub u hu.1
    have hsc := hΦ (x s) hxs (x (s + 1)) hz
    have hL := hgL s h1 h2
    have hnorm : g s (x s - x (s + 1)) ≤ L * ‖x s - x (s + 1)‖ := by
      calc g s (x s - x (s + 1)) ≤ ‖g s (x s - x (s + 1))‖ := le_abs_self _
        _ ≤ ‖g s‖ * ‖x s - x (s + 1)‖ := (g s).le_opNorm _
        _ ≤ L * ‖x s - x (s + 1)‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    -- η g s = Φ'(x s) - Φ'(y(s+1))
    have hg : ∀ v, η * g s v = Φ' (x s) v - Φ' (y (s + 1)) v := by
      intro v
      have := congrArg (fun φ : E →L[ℝ] ℝ => φ v) hgrad
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
      linarith
    have e1 := hg (x s - u)
    have e2 := hg (x s - x (s + 1))
    simp only [ContinuousLinearMap.sub_apply] at hopt
    unfold bregman
    -- linearity expansions
    have lin1 : ∀ φ : E →L[ℝ] ℝ, φ (x s - u) = φ (x s - x (s + 1)) - φ (u - x (s + 1)) := by
      intro φ; rw [← map_sub]; congr 1; abel
    have lin2 : ∀ φ : E →L[ℝ] ℝ, φ (u - x s) = φ (u - x (s + 1)) - φ (x s - x (s + 1)) := by
      intro φ; rw [← map_sub]; congr 1; abel
    have lin3 : ∀ φ : E →L[ℝ] ℝ, φ (x (s + 1) - x s) = - φ (x s - x (s + 1)) := by
      intro φ; rw [← map_neg]; congr 1; abel
    rw [lin1] at e1
    have hq : η * L * ‖x s - x (s + 1)‖ - ρ / 2 * ‖x s - x (s + 1)‖ ^ 2 ≤ C := by
      rw [hC, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (η * L - ρ * ‖x s - x (s + 1)‖)]
    have hsg' : f (x s) - f u ≤ g s (x s - u) := hsg
    rw [lin1] at hsg'
    have hgu := hg (u - x (s + 1))
    rw [lin2]
    nlinarith [mul_le_mul_of_nonneg_left hsg' hη.le, mul_le_mul_of_nonneg_left hnorm hη.le]
  -- telescoping
  have htel : ∀ n, n ≤ t → η * ∑ s ∈ Finset.Icc 1 n, (f (x s) - f u) ≤
      bregman Φ Φ' u (x 1) - bregman Φ Φ' u (x (n + 1)) + n * C := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_Icc_succ_top (by omega), mul_add]
      have := hone (n + 1) (by omega) hn
      have := ih (by omega)
      push_cast
      linarith
  have hfin := htel t le_rfl
  have hlast := hΦ (x (t + 1)) (hmem (t + 1) (by omega) le_rfl) u hu
  have hnn : 0 ≤ bregman Φ Φ' u (x (t + 1)) := by
    unfold bregman
    have : Φ' (x (t + 1)) (u - x (t + 1)) = - Φ' (x (t + 1)) (x (t + 1) - u) := by
      rw [← map_neg]; congr 1; abel
    rw [this]
    nlinarith [sq_nonneg ‖x (t + 1) - u‖]
  rw [div_add' _ _ _ hη.ne', le_div_iff₀ hη]
  have : (η * (L ^ 2 * t / (2 * ρ))) * η = t * C := by
    rw [hC]; field_simp
  nlinarith [this]
