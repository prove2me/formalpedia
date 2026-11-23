-- Prove2me | solution 1 for Csg.idsRoundHealthy_measure_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:00:18.327956+00:00
-- url     : https://prove2.me/submissions/1222cee4-5a2c-45ef-a609-b8a2131ebc5e

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_IntrusionDetectionRecurrence
import Theorems.Thm_Csg_idsRoundPMF_healthy
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
open MeasureTheory Measure ProbabilityTheory
variable (q : ℕ → PMF AttackAction)
namespace Csg
theorem _root_.solution (n : ℕ) :
    (idsPlayMeasure q) {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true}
      = 1 / 2 := by
  have hSet : {p : PolicyAction × AttackAction | idsRoundHealthy p = true} =
      {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} := by
    ext p; simp [idsRoundHealthy]
  have hT : MeasurableSet {p : PolicyAction × AttackAction | idsRoundHealthy p = true} :=
    MeasurableSet.of_discrete
  have heq : {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true} =
      (fun x : ℕ → PolicyAction × AttackAction => x n) ⁻¹'
        {p : PolicyAction × AttackAction | idsRoundHealthy p = true} := rfl
  rw [heq, ← Measure.map_apply (measurable_pi_apply n) hT]
  unfold idsPlayMeasure
  rw [infinitePi_map_eval, (idsRoundPMF q n).toMeasure_apply_eq_toOuterMeasure_apply hT, hSet,
    idsRoundPMF_healthy]
end Csg
