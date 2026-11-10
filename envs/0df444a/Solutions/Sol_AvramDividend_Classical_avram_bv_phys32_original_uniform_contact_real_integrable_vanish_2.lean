-- Prove2me | solution 2 for AvramDividend.Classical.avram_bv_phys32_original_uniform_contact_real_integrable_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:37:21.760949+00:00
-- url     : https://prove2.me/submissions/32b4bfeb-60ce-4f05-86ca-41a9b5edd903

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess29_original_finite_BV_collision_and_width_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess26_original_grid_drift_deficit_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- Convert the exact original fullmark/occupied-cell uniform contact mass to real L1. -/
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
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    N ω - K n ω + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω
  change (∀ n, Integrable (fun ω => (F n ω).toReal) P) ∧
    Tendsto (fun n => ∫ ω, (F n ω).toReal ∂P) atTop (nhds (0 : ℝ))
  have hTr : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hT
  have hStrict (n : ℕ) : StrictMono (u n) := by
    intro i j hij
    apply NNReal.coe_lt_coe.mp
    rw [huniform n i, huniform n j]
    apply div_lt_div_of_pos_right _ (by positivity)
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hTr
  have hZero (n : ℕ) : u n 0 = 0 := by
    apply NNReal.coe_injective
    simpa only [huniform, Nat.cast_zero, mul_zero, zero_div, NNReal.coe_zero]
  have hEnd (n : ℕ) : u n (n + 2) = T := by
    apply NNReal.coe_injective
    rw [huniform n (n + 2)]
    push_cast
    field_simp
  have hdelta : Tendsto
      (fun n : ℕ => (T : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0) := by
    have hc := (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
      (T : ℝ) hTr).2
    have hs := (show Tendsto (fun _ : ℕ => (T : ℝ)) atTop (nhds (T : ℝ)) from tendsto_const_nhds).sub hc
    convert hs using 1
    · funext n; ring
    · ring
  have hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in (atTop : Filter ℕ), ∀ i : ℕ, i < n + 2 →
        dist (u n i) (u n (i + 1)) < δ := by
    intro δ hδ
    filter_upwards [hdelta.eventually (Iio_mem_nhds hδ)] with n hn
    intro i hi
    rw [NNReal.dist_eq, huniform n i, huniform n (i + 1)]
    have heq : (T : ℝ) * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) -
        (T : ℝ) * (i : ℝ) / ((n : ℝ) + 2) =
        (T : ℝ) / ((n : ℝ) + 2) := by
      push_cast
      ring
    rw [abs_sub_comm, heq, abs_of_pos (div_pos hTr (by positivity))]
    exact hn
  have hENN : Tendsto (fun n => ∫⁻ ω, F n ω ∂P)
      atTop (nhds (0 : ℝ≥0∞)) := by
    change Tendsto (fun n => ∫⁻ ω,
      N ω - K n ω + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω ∂P)
      atTop (nhds (0 : ℝ≥0∞))
    exact avram_bv_excess29_original_finite_BV_collision_and_width_L1
      X hBV hFinite T hT u (fun n => n + 2)
      hStrict hZero hEnd hMesh
  have hmN : Measurable N := by
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le)
      Set.univ MeasurableSet.univ
  have hmK (n : ℕ) : Measurable (K n) := by
    exact avram_bv_excess26_original_grid_drift_deficit_count_measurable
      X (u n) (n + 2)
  have hmF (n : ℕ) : Measurable (F n) :=
    (hmN.sub (hmK n)).add (measurable_const.mul hmN)
  have hNmean : (∫⁻ ω, N ω ∂P) < ⊤ := by
    change (∫⁻ ω, ((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) < ⊤
    rw [avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
      X hBV hFinite 0 T (show (0 : ℝ≥0) ≤ T by exact zero_le)]
    exact ENNReal.mul_lt_top (by simp) hFinite
  have hFmean (n : ℕ) : (∫⁻ ω, F n ω ∂P) < ⊤ := by
    have hbound (ω : Ω) :
        F n ω ≤ (1 + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹)) * N ω := by
      calc
        F n ω ≤ N ω + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * N ω :=
          add_le_add_left (tsub_le_self) _
        _ = (1 + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹)) * N ω := by
          rw [add_mul, one_mul]
    calc
      (∫⁻ ω, F n ω ∂P) ≤
          ∫⁻ ω, (1 + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹)) * N ω ∂P :=
        lintegral_mono hbound
      _ = (1 + (((n + 2 : ℕ) : ℝ≥0∞)⁻¹)) * (∫⁻ ω, N ω ∂P) :=
        lintegral_const_mul _ hmN
      _ < ⊤ := ENNReal.mul_lt_top (by simp) hNmean
  constructor
  · intro n
    exact integrable_toReal_of_lintegral_ne_top
      (hmF n).aemeasurable (ne_of_lt (hFmean n))
  · have hReal : Tendsto (fun n => (∫⁻ ω, F n ω ∂P).toReal)
        atTop (nhds (0 : ℝ)) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using
        ((ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hENN)
    have hEq (n : ℕ) :
        (∫ ω, (F n ω).toReal ∂P) = (∫⁻ ω, F n ω ∂P).toReal :=
      integral_toReal (hmF n).aemeasurable
        (ae_lt_top (hmF n) (ne_of_lt (hFmean n)))
    simpa only [hEq] using hReal
