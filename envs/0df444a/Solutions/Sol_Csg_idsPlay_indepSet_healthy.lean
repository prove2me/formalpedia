-- Prove2me | solution 1 for Csg.idsPlay_indepSet_healthy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:00:08.172643+00:00
-- url     : https://prove2.me/submissions/b80b4b17-4d5f-478e-868a-3427a75349d2

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_IntrusionDetectionRecurrence
import Theorems.Thm_Csg_idsRoundHealthy_measurable
import Theorems.Thm_Csg_idsPlay_indepFun_healthy

set_option autoImplicit true
open Csg
open MeasureTheory Measure ProbabilityTheory
variable (q : ℕ → PMF AttackAction)
namespace Csg
theorem _root_.solution :
    iIndepSet (fun n => {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true})
      (idsPlayMeasure q) := by
  have hmeas : ∀ n, MeasurableSet
      {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true} := fun n =>
    (idsRoundHealthy_measurable.comp (measurable_pi_apply n)) (measurableSet_singleton true)
  rw [iIndepSet_iff_iIndepSets_singleton hmeas, iIndepSets_singleton_iff]
  intro t
  have h := idsPlay_indepFun_healthy q
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  exact h t (sets := fun _ => ({true} : Set Bool)) fun _ _ => measurableSet_singleton true
end Csg
