-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_marked_collision_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:01:41.34506+00:00
-- url     : https://prove2.me/submissions/28614a19-0b88-477a-9f10-9100dbaae1af

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_shortcell_original_marked_bochner_range
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_strict_finite_set_card_le_closed
import Theorems.Thm_AvramDividend_Classical_avram_redux18_original_count_marked_collision_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Apply the proved original count/marked collision inequality to the literal
negative marks, masking all time indices outside the selected finite band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    0 ≤ ∫ ω, (W ω - (1 - L ω)) ∂P ∧
    (∫ ω, (W ω - (1 - L ω)) ∂P) ≤
      (1 / ((n : ℝ) + 1)) ^ 2 *
      ((X.ν (Iic (-(1 / ((k : ℝ) + 1))))).toReal) ^ 2 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let q : Ω → ℝ≥0 → ℝ := fun ω u =>
    if u ∈ S ω then
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    else 1
  have hcard (ω : Ω) : (S ω).card ≤
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((k : ℝ) + 1))}.ncard := by
    simpa only [S] using
      (avram_bv_jump8_turn10_strict_finite_set_card_le_closed X ω T k)
  have hqpos (ω : Ω) (u : ℝ≥0) : 0 ≤ q ω u := by
    by_cases hu : u ∈ S ω
    · simp [q, hu, le_of_lt (Real.exp_pos _)]
    · simp [q, hu]
  have hqle (ω : Ω) (u : ℝ≥0) : q ω u ≤ 1 := by
    by_cases hu : u ∈ S ω
    · have hm : 0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
            -(1 / ((k : ℝ) + 1)) := by
        simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hu
      have hden : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hdiv : (0 : ℝ) < 1 / ((k : ℝ) + 1) := one_div_pos.mpr hden
      have hcut : -(1 / ((k : ℝ) + 1)) < 0 := by linarith
      have hjump :
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 :=
        le_of_lt (lt_trans hm.2.2 hcut)
      simp only [q, if_pos hu]
      calc
        Real.exp _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hjump
        _ = 1 := by simp
    · simp [q, hu]
  have hprod (ω : Ω) :
      (∏ u ∈ S ω, q ω u) = W ω := by
    change (S ω).prod (q ω) = (S ω).prod
      (fun u => Real.exp (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    apply Finset.prod_congr rfl
    intro u hu
    simp only [q, if_pos hu]
  have hsum (ω : Ω) :
      (∑ u ∈ S ω, (1 - q ω u)) = L ω := by
    change (S ω).sum (fun u => 1 - q ω u) = (S ω).sum
      (fun u => 1 - Real.exp (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    apply Finset.sum_congr rfl
    intro u hu
    simp only [q, if_pos hu]
  have hint : Integrable W P ∧ Integrable L P ∧
      0 ≤ (∫ ω, W ω ∂P) ∧ (∫ ω, W ω ∂P) ≤ 1 := by
    simpa only [T, S, W, L] using
      (avram_bv_jump8_turn10_shortcell_original_marked_bochner_range
        X hX hBV k n)
  have heq (ω : Ω) :
      ((∏ u ∈ S ω, q ω u) -
        (1 - ∑ u ∈ S ω, (1 - q ω u))) =
      W ω - (1 - L ω) := by
    rw [hprod ω, hsum ω]
  have hE : Integrable (fun ω =>
      ((∏ u ∈ S ω, q ω u) -
        (1 - ∑ u ∈ S ω, (1 - q ω u)))) P := by
    have hfun : (fun ω =>
        ((∏ u ∈ S ω, q ω u) -
          (1 - ∑ u ∈ S ω, (1 - q ω u)))) =
        (fun ω => W ω - (1 - L ω)) := by
      funext ω
      exact heq ω
    rw [hfun]
    exact hint.1.sub ((integrable_const _).sub hint.2.1)
  have hsrc := avram_redux18_original_count_marked_collision_quadratic
    X T k S q hcard hqpos hqle hE
  have heq_int :
      (∫ ω, ((∏ u ∈ S ω, q ω u) -
        (1 - ∑ u ∈ S ω, (1 - q ω u))) ∂P) =
      (∫ ω, (W ω - (1 - L ω)) ∂P) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall heq
  have hr :
      (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((k : ℝ) + 1))))).toReal) =
        (1 / ((n : ℝ) + 1)) *
          (X.ν (Iic (-(1 / ((k : ℝ) + 1))))).toReal := by
    have ht : ((T : ℝ≥0∞).toReal) = 1 / ((n : ℝ) + 1) := by
      rw [ENNReal.coe_toReal]
      simp [T]
    rw [ENNReal.toReal_mul, ht]
  dsimp only at hsrc
  rw [heq_int] at hsrc
  rw [hr] at hsrc
  constructor
  · exact hsrc.1
  · simpa only [mul_pow] using hsrc.2
