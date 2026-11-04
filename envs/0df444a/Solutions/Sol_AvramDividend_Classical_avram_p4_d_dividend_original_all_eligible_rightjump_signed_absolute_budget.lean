-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:47:24.638578+00:00
-- url     : https://prove2.me/submissions/066090a4-5b33-4b5b-aded-c867a7ee014a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_atom_full_signed_and_absolute_budget
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_sparse_rightpayment_subtype_signed_absolute_tsum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Every eligible original right-payment enumeration, including zero payment times, has a signed absolutely summable correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : Function.Injective (fun i : ι => (t i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))
    Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
      Summable (fun i : ι => |J i|) ∧
      (∑' i : ι, |J i|) ≤
        (K - 1) * (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by
  let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
    ((rightLimit D (t i) ω - D (t i) ω) +
      w (x + X.X (t i) ω - rightLimit D (t i) ω) -
      w (riskProcess X x D (t i) ω))
  let S : Set ι := {i | 0 < rightLimit D (t i) ω - D (t i) ω}
  have hNonneg (i : ι) : 0 ≤ rightLimit D (t i) ω - D (t i) ω :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω (t i))
  have hZero (i : ι) (hi : i ∉ S) : J i = 0 := by
    have hn : ¬ 0 < rightLimit D (t i) ω - D (t i) ω := by
      simpa only [S, Set.mem_setOf_eq] using hi
    have hδ : rightLimit D (t i) ω - D (t i) ω = 0 :=
      le_antisymm (le_of_not_gt hn) (hNonneg i)
    have heq : rightLimit D (t i) ω = D (t i) ω := sub_eq_zero.mp hδ
    simp [J, heq, riskProcess]
  have hInjS : Function.Injective (fun a : S => (t a.val : ℝ)) := by
    intro a b hab
    exact Subtype.ext (hInj hab)
  have hPosS : ∀ a : S, 0 < rightLimit D (t a.val) ω - D (t a.val) ω := by
    intro a
    simpa only [S, Set.mem_setOf_eq] using a.property
  obtain ⟨hSummS, hNonposS, hAbsS, hBoundS⟩ :=
    avram_p4_d_dividend_original_positive_atom_full_signed_and_absolute_budget
      X x q hq D hD w hjump (fun a : S => t a.val) ω T
      (fun a => hT a.val) (fun a => hPre a.val)
      (fun a => hPay a.val) hPosS hInjS K hK
      (fun a => hLocalSecant a.val)
  exact avram_p4_d_dividend_sparse_rightpayment_subtype_signed_absolute_tsum
    S J ((K - 1) * (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
      then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal)
    hZero hSummS hNonposS hAbsS hBoundS
