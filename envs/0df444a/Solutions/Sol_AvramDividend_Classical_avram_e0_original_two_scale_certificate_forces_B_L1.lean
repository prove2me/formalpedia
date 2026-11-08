-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_original_two_scale_certificate_forces_B_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:54:54.325509+00:00
-- url     : https://prove2.me/submissions/4bb5fccb-a289-4a61-834c-740ef652f1a2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_value_borel
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_BV_generator_borel_gridfree
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
import Theorems.Thm_AvramDividend_Classical_avram_route_finite_t3_original_all_grid_B_nonpositive_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The exact original stopped two-scale inequality forces integrability of its signed B grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
        (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1)))))
    (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ)
    (hTop : C = ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    (∀ n k, Integrable (M n k) P) →
    (∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P) →
    (∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P) →
    (∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n k ω + B n ω) +
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0) →
    ∀ n, Integrable (B n) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
  change (∀ n k, Integrable (M n k) P) →
    (∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P) →
    (∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P) →
    (∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n k ω + B n ω) +
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0) →
    ∀ n, Integrable (B n) P
  intro hMI hECI hETI hBudget n
  have hw_meas : Measurable w :=
    avram_a19_value_borel X hX hBV q hq w C hC hw_cont hw0
      hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump T hT u hgrid hmono huniform
  have hgen_meas : Measurable (fun y : ℝ => X.generator w y) :=
    avram_bv_meas7_original_BV_generator_borel_gridfree X hBV w hw_meas
  have hBmeas : AEStronglyMeasurable (B n) P := by
    convert
      (avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_of_generator
        X hX hBV q w hw_meas hgen_meas C x D hD u n) using 1
    exact funext (fun ω => hB n ω)
  have hFInt : Integrable (F n) P :=
    avram_p3_comp8_original_canonical_strict_prefix_integrable
      X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg n
  have hRInt : Integrable (fun ω : Ω =>
      w x + M n 0 ω + max (ErrCell n 0 ω) 0 +
        max (ErrContact n 0 ω) 0 - F n ω) P := by
    exact ((((integrable_const _).add (hMI n 0)).add
      (hECI n 0)).add (hETI n 0)).sub hFInt
  have hSign :=
    avram_route_finite_t3_original_all_grid_B_nonpositive_ae
      X hBV x C D w q hw_gen hw_grad u hmono B hB
  apply hRInt.mono' hBmeas
  filter_upwards [hSign, hBudget n 0] with ω hsign hbudget
  have hb : B n ω ≤ 0 := hsign n
  have hbound : -(B n ω) ≤
      w x + M n 0 ω + max (ErrCell n 0 ω) 0 +
        max (ErrContact n 0 ω) 0 - F n ω := by
    linarith
  have hr : 0 ≤ w x + M n 0 ω + max (ErrCell n 0 ω) 0 +
      max (ErrContact n 0 ω) 0 - F n ω :=
    le_trans (neg_nonneg.mpr hb) hbound
  simp only [Real.norm_eq_abs, abs_of_nonpos hb, abs_of_nonneg hr]
  exact hbound
