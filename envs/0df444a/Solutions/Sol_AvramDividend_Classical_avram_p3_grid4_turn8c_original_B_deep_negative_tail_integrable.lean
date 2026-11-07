-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_turn8c_original_B_deep_negative_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:27:47.435948+00:00
-- url     : https://prove2.me/submissions/32f76d87-26ee-494c-a24d-c8e498f9110d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The authentic strict stopped dividend cash plus surviving terminal is
nonnegative. A finite signed physical source B, if measurable and almost surely
nonpositive, is automatically L1 once its cash budget has a centred L1
martingale and an L1 positive error. No global derivative bound is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (S : ℝ≥0)
    (hS : S = ⟨T, hT⟩) (δ : ℕ → ℝ)
    (Pay M B Err : ℕ → Ω → ℝ)
    (hPayExact : ∀ n ω, Pay n ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
         Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0))
    (hM : ∀ n, Integrable (M n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (B n) P)
    (hBNeg : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPayPos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Pay n ω)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      Pay n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0) :
    ∀ n, Integrable (fun ω => max (-(B n ω) - max (w x) 0) 0) P := by
  intro n
  have hMaj : Integrable
      (fun ω : Ω => |M n ω| + max (Err n ω) 0) P :=
    (hM n).abs.add (hErr n)
  have hCont : Continuous (fun z : ℝ => max (-z - max (w x) 0) 0) := by
    fun_prop
  have hMeas : AEStronglyMeasurable
      (fun ω : Ω => max (-(B n ω) - max (w x) 0) 0) P := by
    simpa only [Function.comp_def] using
      hCont.comp_aestronglyMeasurable (hBMeas n)
  refine Integrable.mono' hMaj hMeas ?_
  filter_upwards [hPayPos n, hPath n] with ω hPos hPathω
  have hMle : M n ω ≤ |M n ω| := le_abs_self _
  have hwle : w x ≤ max (w x) 0 := le_max_left _ _
  have hErrpos : 0 ≤ max (Err n ω) 0 := le_max_right _ _
  have hMpos : 0 ≤ |M n ω| := abs_nonneg _
  have hLe : max (-(B n ω) - max (w x) 0) 0 ≤
      |M n ω| + max (Err n ω) 0 := by
    apply max_le
    · linarith
    · linarith
  have hTailPos : 0 ≤ max (-(B n ω) - max (w x) 0) 0 :=
    le_max_right _ _
  have hSumPos : 0 ≤ |M n ω| + max (Err n ω) 0 :=
    add_nonneg hMpos hErrpos
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg hTailPos, abs_of_nonneg hSumPos] using hLe
