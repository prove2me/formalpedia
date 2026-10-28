-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_scaled_subunit_kernel_scale_identification_no_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:25:53.279759+00:00
-- url     : https://prove2.me/submissions/2c50b314-b2db-42db-8707-e6974ed28520

import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Forgetting pointwise kernel identification preserves every scale-renewal datum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < ρ ∧ ρ < 1 ∧ 0 < b ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ κ x) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      (∀ F : ℕ → ℝ → ℝ,
        F 0 = κ →
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) →
        (∀ x : ℝ, 0 < x →
          IntervalIntegrable
            (fun y : ℝ => b * ∑' n : ℕ,
              if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
        (∀ x : ℝ, 0 < x →
          Real.exp (-(φ * x)) * W x =
            c + ∫ y in (0 : ℝ)..x,
              (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y))) := by
  obtain ⟨φ, c, ρ, b, κ, _, hφ, hroot, hρpos, hρone, hbpos,
    hcont, hanti, hκzero, hκpos, hκL1, hmass, hrep⟩ :=
    bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
      X hX q hq W hW hbv
  exact ⟨φ, c, ρ, b, κ, hφ, hroot, hρpos, hρone, hbpos,
    hcont, hanti, hκzero, hκpos, hκL1, hmass, hrep⟩
