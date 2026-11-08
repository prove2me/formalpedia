-- Prove2me | solution 1 for FrechetPrefs.psi_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:43:32.289573+00:00
-- url     : https://prove2.me/submissions/2e428303-50f3-4322-bb77-a2a5a05b382e

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

open FrechetPrefs in
theorem solution (u : ℝ → ℝ) (hu : IsInadaUtility u) (K θ : ℝ) (hK0 : 0 < K)
    (hθ0 : 0 < θ) :
    (|deriv (deriv u) K| ≤ θ →
      (∀ x, K ≤ x → 0 ≤ 1 + 1 / θ * deriv (deriv u) x) ∧
      MonotoneOn (psi u θ) (Ici K)) ∧
    (|deriv (deriv u) K| < θ →
      (∀ x, K ≤ x → 0 < 1 + 1 / θ * deriv (deriv u) x) ∧
      (∀ x, K ≤ x → 0 < deriv (psi u θ) x) ∧
      StrictMonoOn (psi u θ) (Ici K)) := by
  have hC1 : ContDiffOn ℝ 1 (deriv u) (Ioi 0) :=
    hu.1.deriv_of_isOpen isOpen_Ioi one_add_one_eq_two.le
  have hdiff : DifferentiableOn ℝ (deriv u) (Ioi 0) := hC1.differentiableOn one_ne_zero
  have hd : ∀ x, 0 < x → HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x hx =>
    (hdiff.differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
  have hpsi : ∀ x, 0 < x → HasDerivAt (psi u θ) (1 / θ * deriv (deriv u) x + 1) x :=
    fun x hx => ((hd x hx).const_mul (1 / θ)).add (hasDerivAt_id' x)
  have hbound : ∀ x, K ≤ x → |deriv (deriv u) x| ≤ |deriv (deriv u) K| := fun x hx =>
    hu.2.2.2 hK0 (lt_of_lt_of_le hK0 hx) hx
  have hθinv : 1 / θ * (-θ) = -1 := by field_simp
  have hθpos : 0 < 1 / θ := one_div_pos.mpr hθ0
  have hcont : ContinuousOn (psi u θ) (Ici K) := fun x hx =>
    (hpsi x (lt_of_lt_of_le hK0 hx)).continuousAt.continuousWithinAt
  have hdiffI : DifferentiableOn ℝ (psi u θ) (interior (Ici K)) := by
    rw [interior_Ici]
    exact fun x hx => (hpsi x (hK0.trans hx)).differentiableAt.differentiableWithinAt
  refine ⟨fun hθ => ?_, fun hθ => ?_⟩
  · have ha : ∀ x, K ≤ x → 0 ≤ 1 + 1 / θ * deriv (deriv u) x := by
      intro x hx
      have h1 := hbound x hx
      have h2 := neg_abs_le (deriv (deriv u) x)
      have h3 : -θ ≤ deriv (deriv u) x := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hθpos.le
      linarith
    refine ⟨ha, ?_⟩
    apply monotoneOn_of_deriv_nonneg (convex_Ici K) hcont hdiffI
    rw [interior_Ici]
    intro x hx
    rw [(hpsi x (hK0.trans hx)).deriv]
    linarith [ha x (le_of_lt hx)]
  · have ha : ∀ x, K ≤ x → 0 < 1 + 1 / θ * deriv (deriv u) x := by
      intro x hx
      have h1 := hbound x hx
      have h2 := neg_abs_le (deriv (deriv u) x)
      have h3 : -θ < deriv (deriv u) x := by linarith
      have h4 := mul_lt_mul_of_pos_left h3 hθpos
      linarith
    have hb : ∀ x, K ≤ x → 0 < deriv (psi u θ) x := by
      intro x hx
      rw [(hpsi x (lt_of_lt_of_le hK0 hx)).deriv]
      linarith [ha x hx]
    refine ⟨ha, hb, ?_⟩
    apply strictMonoOn_of_deriv_pos (convex_Ici K) hcont
    rw [interior_Ici]
    intro x hx
    exact hb x (le_of_lt hx)
