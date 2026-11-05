-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_L2_product_of_predictable_Linfty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:27:31.140737+00:00
-- url     : https://prove2.me/submissions/6c3eae5f-ad73-42c6-af26-84198ff38346

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- An L² original-space sum multiplied by an essentially bounded predictable coefficient remains L². -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (U V : Ω → ℝ) (hU : MemLp U 2 P) (hV : MemLp V ⊤ P) :
    MemLp (fun ω => U ω * V ω) 2 P := by
  have hProduct : MemLp (V * U) 2 P := hU.mul hV
  convert hProduct using 1
  funext ω
  simp only [Pi.mul_apply]
  ring
