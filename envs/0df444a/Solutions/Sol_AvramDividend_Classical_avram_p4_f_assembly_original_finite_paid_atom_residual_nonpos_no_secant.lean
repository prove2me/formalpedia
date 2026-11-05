-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_paid_atom_residual_nonpos_no_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:54:45.349545+00:00
-- url     : https://prove2.me/submissions/31a4c21f-745e-403d-a123-36dd96aada9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D s ω - D s ω ≤
          w (riskProcess X x D s ω) -
            w (riskProcess X x D s ω -
              (rightLimit D s ω - D s ω)))
    (ω : Ω) (t : ι → ℝ) (S : Finset ι)
    (hPay : ∀ i ∈ S, t i ∈ paymentTimes (ruinTime X x D ω)) :
    (∑ i ∈ S, Real.exp (-(q * t i)) *
      ((rightLimit D (Real.toNNReal (t i)) ω -
        D (Real.toNNReal (t i)) ω) +
        w (x + X.X (Real.toNNReal (t i)) ω -
          rightLimit D (Real.toNNReal (t i)) ω) -
        w (riskProcess X x D (Real.toNNReal (t i)) ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  have hDomain :=
    avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
      X x D ω (t i) (hPay i hi)
  have hPre : Real.toNNReal (t i) = 0 ∨
      ((Real.toNNReal (t i) : ℝ≥0∞) < ruinTime X x D ω) := by
    rcases hDomain with hZero | ⟨_, hBefore⟩
    · exact Or.inl hZero
    · exact Or.inr hBefore
  have hTimeNonneg : 0 ≤ t i :=
    (paymentTimes_membership_to_nNReal_active
      (ruinTime X x D ω) (t i) (hPay i hi)).1
  simpa [Real.coe_toNNReal, max_eq_left hTimeNonneg] using
    (avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
      X x D w q hjump (fun _ => Real.toNNReal (t i)) ω hPre)
