-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys32_original_uniform_contact_real_integrable_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:36:46.995088+00:00
-- url     : https://prove2.me/submissions/eebd08b8-fdaa-47f8-9c15-e6ac3fed75e7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys31_original_uniform_collision_width_joint_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess26_original_grid_drift_deficit_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original joint finite-activity contact error is a real L1 witness with vanishing mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      (T : ℝ) * (i : ℝ) / ((n : ℝ) + 2)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
    let K : ℕ → Ω → ℝ≥0∞ := fun n ω =>
      ∑ i ∈ Finset.range (n + 2),
        if X.X (u n (i + 1)) ω - X.X (u n i) ω <
          X.drift * (((u n (i + 1) - u n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0
    let Err : ℕ → Ω → ℝ := fun n ω =>
      (N ω - K n ω + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω).toReal
    (∀ n, Integrable (Err n) P) ∧
      Filter.Tendsto (fun n => ∫ ω, Err n ω ∂P)
        Filter.atTop (nhds (0 : ℝ)) := by
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
  let K : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∑ i ∈ Finset.range (n + 2),
      if X.X (u n (i + 1)) ω - X.X (u n i) ω <
        X.drift * (((u n (i + 1) - u n i : ℝ≥0) : ℝ))
      then (1 : ℝ≥0∞) else 0
  let E : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    N ω - K n ω + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω
  let Err : ℕ → Ω → ℝ := fun n ω => (E n ω).toReal
  change (∀ n, Integrable (Err n) P) ∧
    Filter.Tendsto (fun n => ∫ ω, Err n ω ∂P)
      Filter.atTop (nhds (0 : ℝ))
  have hmN : Measurable N := by
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le) Set.univ MeasurableSet.univ
  have hmK (n : ℕ) : Measurable (K n) :=
    avram_bv_excess26_original_grid_drift_deficit_count_measurable
      X (u n) (n + 2)
  have hmE (n : ℕ) : Measurable (E n) := by
    exact (hmN.sub (hmK n)).add (measurable_const.mul hmN)
  have hrate : (∫⁻ ω, N ω ∂P) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    simpa only [N, tsub_zero] using
      avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
        X hBV hFinite 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le)
  have hNfin : (∫⁻ ω, N ω ∂P) < ⊤ := by
    rw [hrate]
    exact ENNReal.mul_lt_top (by simp) hFinite
  have hAfin (n : ℕ) :
      (∫⁻ ω, N ω - K n ω ∂P) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => tsub_le_self) hNfin
  have hWfin (n : ℕ) :
      (∫⁻ ω, (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω ∂P) < ⊤ := by
    rw [lintegral_const_mul' _ _ (by finiteness)]
    exact ENNReal.mul_lt_top (by finiteness) hNfin
  have hEfin (n : ℕ) : (∫⁻ ω, E n ω ∂P) < ⊤ := by
    change (∫⁻ ω, (N - K n) ω +
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω ∂P) < ⊤
    rw [lintegral_add_left (hmN.sub (hmK n))]
    exact ENNReal.add_lt_top.mpr ⟨hAfin n, hWfin n⟩
  have hintegrable (n : ℕ) : Integrable (Err n) P := by
    exact MeasureTheory.integrable_toReal_of_lintegral_ne_top
      (hmE n).aemeasurable (ne_of_lt (hEfin n))
  have hint (n : ℕ) :
      (∫ ω, Err n ω ∂P) = (∫⁻ ω, E n ω ∂P).toReal := by
    exact MeasureTheory.integral_toReal (hmE n).aemeasurable
      (ae_lt_top (hmE n) (ne_of_lt (hEfin n)))
  have hlim : Filter.Tendsto (fun n => ∫⁻ ω, E n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    exact avram_bv_phys31_original_uniform_collision_width_joint_L1
      X hBV hFinite T hT u huniform
  have hlimR : Filter.Tendsto
      (fun n => (∫⁻ ω, E n ω ∂P).toReal)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hlim
  exact ⟨hintegrable, hlimR.congr'
    (Filter.Eventually.of_forall fun n => (hint n).symm)⟩
