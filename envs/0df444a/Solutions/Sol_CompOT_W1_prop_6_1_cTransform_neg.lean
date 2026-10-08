-- Prove2me | solution 1 for CompOT.W1.prop_6_1_cTransform_neg
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T10:17:17.848511+00:00
-- url     : https://prove2.me/submissions/b06958a4-ed8f-42d3-bc62-18e261d1376f

import Mathlib
import Definitions.Def_CompOT_W1_Defs

open CompOT.W1

theorem solution {X : Type*} [MetricSpace X] (f : X → ℝ)
    (hf : LipschitzWith 1 f) :
    ∀ y, cTransform (fun x => -f x) y = (f y : EReal) := by
  intro y
  unfold cTransform MongeKantorovichYao.cConjugate distCost
  apply le_antisymm
  · exact (iInf_le _ y).trans (by simp)
  · refine le_iInf (fun x => ?_)
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h := hf.le_add_mul y x
    simp only [NNReal.coe_one, one_mul, dist_comm y x] at h
    linarith

#print axioms solution
