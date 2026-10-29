-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_grid_capped_NNReal_stopping_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:12:39.680992+00:00
-- url     : https://prove2.me/submissions/ae2ac7ac-0a48-421e-be18-dceeb3d75ca6

import Mathlib
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_observation_or_horizon_stopping_ws01c

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Ω → ℝ) (b : ℝ) (H T : ℝ≥0)
    (L : List ℝ≥0)
    (hL : ∀ t ∈ L, t ≤ H)
    (hY : ∀ t, Measurable[ℱ t] (Y t)) :
    IsStoppingTime ℱ
      (fun ω => (((bv_finite_grid_below_NNReal_ws01c Y b H L ω) ⊓ T) :
        WithTop ℝ≥0)) := by
  have key : IsStoppingTime ℱ (fun ω => ((bv_finite_grid_below_NNReal_ws01c Y b H L ω : ℝ≥0) :
      WithTop ℝ≥0)) := by
    unfold bv_finite_grid_below_NNReal_ws01c
    induction L with
    | nil => exact isStoppingTime_const ℱ H
    | cons a L ih =>
      simp only [List.foldr_cons, WithTop.coe_min]
      have h1 := bv_observation_or_horizon_stopping_ws01c ℱ (Y a) a H (hL a List.mem_cons_self)
        (hY a) b
      exact h1.min (ih fun t ht => hL t (List.mem_cons_of_mem a ht))
  show IsStoppingTime ℱ (fun ω => min ((bv_finite_grid_below_NNReal_ws01c Y b H L ω : ℝ≥0) : WithTop ℝ≥0) (T : WithTop ℝ≥0))
  exact key.min (isStoppingTime_const ℱ T)
