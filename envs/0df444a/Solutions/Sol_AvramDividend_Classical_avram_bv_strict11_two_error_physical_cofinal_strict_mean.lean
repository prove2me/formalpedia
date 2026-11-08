-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict11_two_error_physical_cofinal_strict_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:55:12.284707+00:00
-- url     : https://prove2.me/submissions/bab54b5a-6577-4dd3-9fea-23d0e162d250

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_two_scale_centered_positive_error_diagonal
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Source-faithful diagonal of two independent physical errors followed by the original stopped-cash cofinal expectation bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hu : Monotone u) (hu0 : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ)) (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) (F B : ℕ → Ω → ℝ)
    (hF : ∀ n ω, F n ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0))
    (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ) (η : ℕ → ℝ) (hηpos : ∀ n, 0 < η n) (hηzero : Tendsto η atTop (nhds (0 : ℝ)))
    (hM : ∀ n k, Integrable (M n k) P ∧
      (∫ ω, M n k ω ∂P) = 0)
    (hCell : ∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P) (hContact : ∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P) (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hBudget : ∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n k ω + B n ω) +
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0)
    (hApprox : ∀ n (ε : ℝ), 0 < ε → ∃ k,
      (∫ ω, max (ErrCell n k ω) 0 ∂P) +
        (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε) :
    (∫ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  let Err : ℕ → ℕ → Ω → ℝ := fun n k ω => max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0
  have hEq (n k : ℕ) (ω : Ω) :
      max (Err n k ω) 0 =
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0 := by
    exact max_eq_left (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have hErrInt (n k : ℕ) : Integrable (fun ω => max (Err n k ω) 0) P := by
    have hFun : (fun ω => max (Err n k ω) 0) =
        (fun ω => max (ErrCell n k ω) 0) +
          (fun ω => max (ErrContact n k ω) 0) := by
      funext ω
      simpa only [Pi.add_apply] using hEq n k ω
    rw [hFun]
    exact (hCell n k).add (hContact n k)
  have hApprox' (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ k : ℕ,
        (∫ ω, max (Err n k ω) 0 ∂P) ≤ η n + ε ∧
        (∀ᵐ ω ∂P,
          F n ω ≤ w x + (M n k ω + B n ω) + max (Err n k ω) 0) := by
    obtain ⟨k, hk⟩ := hApprox n ε hε
    refine ⟨k, ?_, ?_⟩
    · have hInt :
          (∫ ω, max (Err n k ω) 0 ∂P) =
            (∫ ω, max (ErrCell n k ω) 0 ∂P) +
            (∫ ω, max (ErrContact n k ω) 0 ∂P) := by
          simpa only [hEq, Pi.add_apply] using
            (integral_add (hCell n k) (hContact n k))
      exact hInt.trans_le hk
    · filter_upwards [hBudget n k] with ω hω
      simpa only [hEq n k ω, add_assoc] using hω
  obtain ⟨M', Err', hM', hErr', hErrMean', hPath'⟩ :=
    AvramDividend.Classical.avram_bv_strict6_two_scale_centered_positive_error_diagonal
      P F B (w x) M Err η hηpos hηzero hM hErrInt hApprox'
  apply AvramDividend.Classical.avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
    X hBV x C D hD w hw_cont hw_neg q hq S u hu hu0 hbelow hcover
    M' B Err'
  · exact fun n => ⟨(hM' n).1, le_of_eq (hM' n).2⟩
  · exact hB
  · exact hErr'
  · exact hErrMean'
  · intro n
    filter_upwards [hPath' n] with ω hω
    rw [← hF n ω]
    exact hω
