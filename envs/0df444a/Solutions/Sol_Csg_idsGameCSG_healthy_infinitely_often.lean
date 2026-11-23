-- Prove2me | solution 1 for Csg.idsGameCSG_healthy_infinitely_often
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:39.39203+00:00
-- url     : https://prove2.me/submissions/a548af4d-9606-4c85-8f68-8754695e95fb

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_IntrusionDetectionRecurrence
import Theorems.Thm_Csg_idsRoundHealthy_measurable
import Theorems.Thm_Csg_idsRoundHealthy_measure_true
import Theorems.Thm_Csg_idsPlay_indepSet_healthy
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
open MeasureTheory Measure ProbabilityTheory
variable (q : ℕ → PMF AttackAction)
namespace Csg
theorem _root_.solution :
    (idsPlayMeasure q)
      (Filter.limsup (fun n => {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true})
        Filter.atTop) = 1 := by
  apply measure_limsup_eq_one
  · exact fun n => (idsRoundHealthy_measurable.comp (measurable_pi_apply n))
      (measurableSet_singleton true)
  · exact idsPlay_indepSet_healthy q
  · simp only [idsRoundHealthy_measure_true q]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)
end Csg
