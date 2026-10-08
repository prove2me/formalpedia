-- Prove2me | solution 1 for CompOT.W1.prop_6_1_cTransform_self
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T10:18:59.285479+00:00
-- url     : https://prove2.me/submissions/dadd613b-39ec-4db4-b956-ed4b472aa8d3

import Mathlib
import Definitions.Def_CompOT_W1_Defs

open CompOT.W1

theorem solution {X : Type*} [MetricSpace X] (f : X → ℝ)
    (hf : LipschitzWith 1 f) :
    ∀ y, cTransform f y = ((-f y : ℝ) : EReal) := by
  intro y
  unfold cTransform MongeKantorovichYao.cConjugate distCost
  apply le_antisymm
  · exact (iInf_le _ y).trans (by simp)
  · refine le_iInf (fun x => ?_)
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h := hf.le_add_mul x y
    simp only [NNReal.coe_one, one_mul] at h
    linarith

#print axioms solution
