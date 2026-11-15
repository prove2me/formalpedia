-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a62_original_BV_strict_prehorizon_ruinclipped_expected_physical_supermartingale_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:56:11.073952+00:00
-- url     : https://prove2.me/submissions/bb16cc60-d564-4815-a2e7-4a758d5a7dc6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_finitecap_original_strict_physical_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_redux6_bv_single_clock_top_cap_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ (r : ℝ≥0), 0 < r → (r : ℝ) < T →
      (∫⁻ ω, ENNReal.ofReal
        ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
         (if (r : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (r : ℝ))) * w (riskProcess X x D r ω) else 0)) ∂P) ≤
        ENNReal.ofReal (w x) := by
  classical
  intro r hr hrT
  let R : ℝ := (r : ℝ)
  have hRpos : 0 < R := by exact_mod_cast hr
  have hrEq : (⟨R, le_of_lt hRpos⟩ : ℝ≥0) = r := Subtype.ext rfl
  let δ : ℕ → ℝ := fun n => R / ((n : ℝ) + 2)
  let u : ℕ → ℝ := fun n => R - δ n
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ R := by
    dsimp [δ]; apply div_le_self (le_of_lt hRpos)
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  have hMono : Monotone u := by
    intro i j hij
    have hi : 0 < (i : ℝ) + 2 := by positivity
    have hijr : ((i : ℝ) + 2) ≤ (j : ℝ) + 2 := by exact_mod_cast (Nat.add_le_add_right hij 2)
    have hh := div_le_div_of_nonneg_left (le_of_lt hRpos) hi hijr
    dsimp [u, δ]; linarith
  have hNonnegClock (n : ℕ) : 0 ≤ u n := by dsimp [u]; linarith [hδle n]
  have hBelow (n : ℕ) : u n ≤ R := by dsimp [u]; linarith [hδpos n]
  have hShift : Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1))
      atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
  have hOne : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
      atTop (𝓝 0) := by
    convert hShift using 1; funext n; congr 1; push_cast; ring
  have hδT : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
    simpa only [δ, div_eq_mul_inv, one_mul, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => R) atTop (𝓝 R)).mul hOne)
  have hUT : Tendsto u atTop (𝓝 R) := by
    simpa only [u, sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => R) atTop (𝓝 R)).sub hδT)
  have hCover : ∀ s : ℝ, s < R → ∃ n, s < u n := by
    intro s hs; exact (hUT.eventually (isOpen_Ioi.mem_nhds hs)).exists
  let Q : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio R,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (r : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * R)) * w (riskProcess X x D r ω) else 0)
  have hMesh (n : ℕ) :
      (∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (r : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * R)) * w (riskProcess X x D r ω) else 0) ∂P) ≤ w x := by
    by_cases hTop : C = ⊤
    · have hs : u n < R := by dsimp [u]; linarith [hδpos n]
      have hh := avram_redux6_bv_single_clock_top_cap_expected_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD
        hw_nonneg hjump R (le_of_lt hRpos) hRpos hTop
        (u n) (hNonnegClock n) hs
      simpa only [R, u, δ, hrEq] using hh
    · have hh := avram_bv_finitecap_original_strict_physical_expected_cash_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD
        hw_nonneg hjump R hRpos hTop n
      simpa only [R, u, δ, hrEq] using hh
  have hMean : (∫ ω, Q ω ∂P) ≤ w x := by
    have hh := avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
      X hBV x C D hD w hw_cont hw_neg q hq.le r u hMono
      hNonnegClock hBelow hCover (w x) hMesh
    simpa only [Q, R, hrEq] using hh
  have hI : Integrable Q P := by
    have hh := avram_p3_bv_original_prebudget_L1
      X hBV x C D hD w hw_cont hw_neg q hq.le R (le_of_lt hRpos)
    simpa only [Q, R, hrEq] using hh
  have hQnonneg : ∀ᵐ ω ∂P, 0 ≤ Q ω := by
    filter_upwards [] with ω; dsimp only [Q]
    apply add_nonneg ENNReal.toReal_nonneg
    split_ifs with hs
    · exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hw_nonneg ω r hr hs)
    · exact le_refl 0
  have hResult := avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
      (fun (_ : ℕ) => Q) (w x)
      (fun _ => hI) (fun _ => hQnonneg) (fun _ => hMean) 0
  simpa only [Q, R] using hResult
