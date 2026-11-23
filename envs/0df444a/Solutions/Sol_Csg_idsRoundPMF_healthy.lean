-- Prove2me | solution 1 for Csg.idsRoundPMF_healthy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:58:15.444773+00:00
-- url     : https://prove2.me/submissions/49b1eb0c-d17b-4ca9-8a96-3a0a080b77e7

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_IntrusionDetectionRecurrence
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
open MeasureTheory Measure ProbabilityTheory
variable (q : ℕ → PMF AttackAction)
namespace Csg
theorem _root_.solution (n : ℕ) :
    (idsRoundPMF q n).toOuterMeasure {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy}
      = 1 / 2 := by
  have huniv :
      (Finset.univ : Finset PolicyAction) = {PolicyAction.defend1, PolicyAction.defend2} := by
    decide
  have huniv2 :
      (Finset.univ : Finset AttackAction) = {AttackAction.attack1, AttackAction.attack2} := by
    decide
  have huniform : ∀ a1 : PolicyAction, (PMF.uniformOfFintype PolicyAction) a1 = 1 / 2 := by
    intro a1
    rw [PMF.uniformOfFintype_apply]
    norm_num [show Fintype.card PolicyAction = 2 from by decide]
  have hD1 : (PMF.map (fun a2 => (PolicyAction.defend1, a2)) (q n)).toOuterMeasure
      {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} = q n .attack1 := by
    rw [PMF.toOuterMeasure_map_apply]
    have hpre : (fun a2 => (PolicyAction.defend1, a2)) ⁻¹'
        {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} =
        {AttackAction.attack1} := by
      ext a2; cases a2 <;> simp [idsNext]
    rw [hpre, PMF.toOuterMeasure_apply_singleton]
  have hD2 : (PMF.map (fun a2 => (PolicyAction.defend2, a2)) (q n)).toOuterMeasure
      {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} = q n .attack2 := by
    rw [PMF.toOuterMeasure_map_apply]
    have hpre : (fun a2 => (PolicyAction.defend2, a2)) ⁻¹'
        {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy} =
        {AttackAction.attack2} := by
      ext a2; cases a2 <;> simp [idsNext]
    rw [hpre, PMF.toOuterMeasure_apply_singleton]
  have hsum : (q n) .attack1 + (q n) .attack2 = 1 := by
    have htotal := (q n).tsum_coe
    rwa [tsum_fintype, huniv2, Finset.sum_insert (by decide), Finset.sum_singleton] at htotal
  unfold idsRoundPMF
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, huniv,
    Finset.sum_insert (by decide), Finset.sum_singleton, huniform, huniform, hD1, hD2, ← mul_add,
    hsum, mul_one]
end Csg
