-- Prove2me | solution 1 for FeynmanKac.model_pathDiscount_pos_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:11:26.312594+00:00
-- url     : https://prove2.me/submissions/ab723557-9918-4edc-91ef-1c7517003ae6

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FeynmanKac_discount_pos_le_one
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (s : ℝ) (hts : m.initialTime ≤ s) (ω : Ω)
    (hInt : IntervalIntegrable (fun r => m.potential (m.path r ω) r)
        MeasureTheory.volume m.initialTime s) :
    0 < m.pathDiscount s ω ∧ m.pathDiscount s ω ≤ 1 := by
  have hV : ∀ r ∈ Set.Icc m.initialTime s,
      0 ≤ m.potential (m.path r ω) r := by
    intro r hr
    exact m.potential_nonneg (m.path r ω) r
  exact FeynmanKac.discount_pos_le_one m.path m.potential
    m.initialTime s hts ω hV hInt
