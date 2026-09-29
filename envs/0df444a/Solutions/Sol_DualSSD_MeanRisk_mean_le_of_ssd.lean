-- Prove2me | solution 1 for DualSSD.MeanRisk.mean_le_of_ssd
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:59:23.346746+00:00
-- url     : https://prove2.me/submissions/c0008e10-9584-42f8-91d7-525b35c8bea3

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini

namespace DualSSD.MeanRisk

open MeasureTheory

/-- `F_X^(2)(η) = E (η - X)_+` for integrable `X`. -/
theorem aux_mlos_secondPerf_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    Shared.secondPerformance P X η = ∫ ω, max (η - X ω) 0 ∂P := by
  have hf : Integrable (fun ω => max (η - X ω) 0) P := ((integrable_const η).sub hX).pos_part
  rw [hf.integral_eq_integral_meas_le (Filter.Eventually.of_forall fun _ => le_max_right _ _)]
  have h1 : ∫ t in Set.Ioi (0:ℝ), P.real {a | t ≤ max (η - X a) 0}
      = ∫ t in Set.Ioi (0:ℝ), (fun s => Shared.distFun P X (η + s)) (-t) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [Shared.distFun]
    congr 1
    ext a
    simp only [Set.mem_ofPred_eq, le_max_iff]
    have ht' : (0:ℝ) < t := ht
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h
      left
      linarith
  have h3 := integral_comp_neg_Ioi (0:ℝ) (fun s => Shared.distFun P X (η + s))
  rw [h1, h3, neg_zero]
  unfold Shared.secondPerformance
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  have h2 : (Set.Iic (0:ℝ)).indicator (fun s => Shared.distFun P X (η + s))
      = fun s => (Set.Iic η).indicator (Shared.distFun P X) (s + η) := by
    ext s
    by_cases hs : s ≤ 0
    · have : s + η ≤ η := by linarith
      simp [Set.indicator, hs, add_comm]
    · have : ¬ (s + η ≤ η) := by intro h; exact hs (by linarith)
      simp [Set.indicator, hs, this]
  rw [h2, integral_add_right_eq_self (fun s => (Set.Iic η).indicator (Shared.distFun P X) s) η]

theorem aux_mlos_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P) :
    Filter.Tendsto (fun η : ℝ => ∫ ω, max (Y ω - η) 0 ∂P) Filter.atTop (nhds 0) := by
  have h0 : nhds (0:ℝ) = nhds (∫ ω, (0:ℝ) ∂P) := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => |Y ω|) ?_ ?_ hY.abs ?_
  · exact Filter.Eventually.of_forall fun η =>
      ((hY.sub (integrable_const η)).pos_part).aestronglyMeasurable
  · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with η hη
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    linarith [le_abs_self (Y ω)]
  · refine Filter.Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (Y ω)] with η hη
    rw [max_eq_right (by linarith)]

theorem aux_mlos_split {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Integrable Z P) (η : ℝ) :
    ∫ ω, max (η - Z ω) 0 ∂P = η - mean P Z + ∫ ω, max (Z ω - η) 0 ∂P := by
  have e : (fun ω => max (η - Z ω) 0) = fun ω => (η - Z ω) + max (Z ω - η) 0 := by
    ext ω
    rcases le_total (Z ω) η with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have i1 : Integrable (fun ω => η - Z ω) P := (integrable_const η).sub hZ
  have i2 : Integrable (fun ω => max (Z ω - η) 0) P := (hZ.sub (integrable_const η)).pos_part
  rw [e, integral_add i1 i2, integral_sub (integrable_const η) hZ]
  simp [mean]

end DualSSD.MeanRisk

open DualSSD.MeanRisk
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    DualSSD.Shared.SSD P X Y → mean P Y ≤ mean P X := by
  intro h
  have key : ∀ η : ℝ, mean P Y - mean P X ≤ ∫ ω, max (Y ω - η) 0 ∂P := by
    intro η
    have hη := h η
    rw [aux_mlos_secondPerf_eq P X hX η, aux_mlos_secondPerf_eq P Y hY η,
      aux_mlos_split P X hX η, aux_mlos_split P Y hY η] at hη
    have hA : 0 ≤ ∫ ω, max (X ω - η) 0 ∂P :=
      integral_nonneg fun ω => le_max_right _ _
    linarith
  have := ge_of_tendsto' (aux_mlos_tendsto P Y hY) key
  linarith
