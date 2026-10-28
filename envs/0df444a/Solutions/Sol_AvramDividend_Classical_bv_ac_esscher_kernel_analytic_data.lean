-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_kernel_analytic_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:02:17.796931+00:00
-- url     : https://prove2.me/submissions/98daf37d-66dd-482e-97b7-d854c2003b78

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The analytic hypotheses for the corrected BV Esscher renewal identification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ ρ : ℝ) (κ : ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ κ x) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ ∧
      (∀ (b : ℝ) (F : ℕ → ℝ → ℝ),
        F 0 = κ →
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) →
        ∀ x : ℝ, 0 < x →
          IntervalIntegrable
            (fun y : ℝ => b * ∑' n : ℕ,
              if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) := by
  obtain ⟨φ, hφ, hroot⟩ := bv_positive_esscher_root X hX q hq hbv
  obtain ⟨κ, ρ, _hκdef, hρpos, hρlt, hcont, hanti, hzero,
    hpos, hL1, hmass⟩ :=
    bv_esscher_root_positive_subunit_kernel_package
      X hX hbv q hq φ hφ hroot
  refine ⟨φ, ρ, κ, hφ, hroot, hρpos, hρlt, hcont, hanti,
    hzero, ?_, hL1, hmass, ?_⟩
  · intro x _hx
    exact hpos x
  · intro b F hFzero hFrec x hx
    exact (causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
      κ ρ b hρpos hρlt hcont hanti hzero
      (fun y _hy => hpos y) hL1 hmass F hFzero hFrec).2 x hx