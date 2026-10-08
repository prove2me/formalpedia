-- Prove2me | solution 1 for CompOT.W1.prop_6_1_lipschitz_of_cTransform
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T10:18:57.525423+00:00
-- url     : https://prove2.me/submissions/a20b96de-cedb-45c5-b7e1-53e6b7614092

import Definitions.Def_CompOT_W1_Defs

open CompOT.W1

/-- The triangle inequality transfers lower bounds between the two infima. -/
theorem solution {X : Type*} [MetricSpace X] (f g : X → ℝ)
    (hfg : ∀ y, (f y : EReal) = cTransform g y) :
    LipschitzWith 1 f := by
  have hupper (x z : X) : f x ≤ dist z x - g z := by
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_sub, hfg x]
    exact iInf_le (fun w : X => (dist w x : EReal) - (g w : EReal)) z
  have hshift (x y : X) : f x - dist x y ≤ f y := by
    apply EReal.coe_le_coe_iff.mp
    rw [hfg y]
    unfold cTransform MongeKantorovichYao.cConjugate distCost
    refine le_iInf fun z => ?_
    rw [← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    have hz := hupper x z
    have htriangle := dist_triangle z y x
    rw [dist_comm y x] at htriangle
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_le_iff]
  constructor
  · have h := hshift x y
    linarith
  · have h := hshift y x
    rw [dist_comm y x] at h
    linarith

#print axioms solution
