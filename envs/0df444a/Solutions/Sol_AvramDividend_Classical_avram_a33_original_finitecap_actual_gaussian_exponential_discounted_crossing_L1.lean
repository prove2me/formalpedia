-- Prove2me | solution 1 for AvramDividend.Classical.avram_a33_original_finitecap_actual_gaussian_exponential_discounted_crossing_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:42:44.485117+00:00
-- url     : https://prove2.me/submissions/ec1ef205-3554-400d-85af-8626fb5268db

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a32_original_finitecap_actual_gaussian_discounted_crossing_expected_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc a b)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0) P)    (q : ℝ) (hq : 0 ≤ q)
    (ρ : ℕ → Ω → ℝ≥0) (hρmeas : ∀ m, Measurable (ρ m)) :
    Tendsto (fun m => ∫ ω,
      Real.exp (-(q * (ρ m ω : ℝ))) * max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0 ∂P)
       atTop (nhds (0 : ℝ))  := by
  letI : IsProbabilityMeasure P := X.isProbability
  let E : ℕ → Ω → ℝ := fun m ω => Real.exp (-(q * (ρ m ω : ℝ)))
  have hEm : ∀ m, AEStronglyMeasurable (E m) P := by
    intro m
    have hr : Measurable (fun ω => (ρ m ω : ℝ)) :=
      (hρmeas m).coe_nnreal_real
    have he : Measurable (fun ω => Real.exp (-(q * (ρ m ω : ℝ)))) :=
      Real.measurable_exp.comp ((measurable_const.mul hr).neg)
    exact he.aestronglyMeasurable
  have hEb : ∀ m, ∀ᵐ ω ∂P, 0 ≤ E m ω ∧ E m ω ≤ 1 := by
    intro m
    filter_upwards [] with ω
    have hr : 0 ≤ (ρ m ω : ℝ) := NNReal.coe_nonneg _
    have hh : -(q * (ρ m ω : ℝ)) ≤ 0 := neg_nonpos.mpr (mul_nonneg hq hr)
    constructor
    · exact (Real.exp_pos _).le
    · have hExp : Real.exp (-(q * (ρ m ω : ℝ))) ≤ Real.exp (0 : ℝ) :=
        Real.exp_le_exp.mpr hh
      simpa only [Real.exp_zero, E] using hExp
  have ht :=
    avram_a32_original_finitecap_actual_gaussian_discounted_crossing_expected_L1
      X hν T s t hRange hGap w c hc hw_cont hw_neg
      a b r hr hra hab hbc y hy hMeas E hEm hEb
  simpa only [E] using ht
