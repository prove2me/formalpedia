-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilt_origin_of_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:33:25.656036+00:00
-- url     : https://prove2.me/submissions/fb838860-53e8-4fc0-862b-7a22ad5a4699

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Instances.Real.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology

theorem solution
    (φ r : ℝ) (W : ℝ → ℝ)
    (hW : ContinuousWithinAt W (Set.Ioi (0 : ℝ)) 0)
    (htilt : Tendsto (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds r)) :
    W 0 = r := by
  have he : ContinuousAt (fun x : ℝ => Real.exp (-(φ * x))) 0 := by
    fun_prop
  have hc : ContinuousWithinAt
      (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (Set.Ioi (0 : ℝ)) 0 :=
    he.continuousWithinAt.mul hW
  have hlim : Tendsto (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W 0)) := by
    simpa using hc.tendsto
  exact tendsto_nhds_unique hlim htilt
