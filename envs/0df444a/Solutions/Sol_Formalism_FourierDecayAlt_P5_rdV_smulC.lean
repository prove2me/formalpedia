-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.rdV_smulC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:03.396253+00:00
-- url     : https://prove2.me/submissions/75d0c32c-128a-4655-9207-5935ae0b920b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_snd
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_add_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_add_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_alg_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_alg_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_mul_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_mul_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_one_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_one_snd
attribute [local simp] P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
attribute [local simp] P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e



set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) : SmulC (E := E) (RdV X) := by
  intro α f
  funext g
  simp only [RdV, Pi.smul_apply]
  first
    | exact deriv_const_smul' α
    | (by_cases h : DifferentiableAt ℝ (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
       · exact deriv_const_smul α h
       · by_cases hα : α = 0
         · subst hα; simp
         · rw [deriv_zero_of_not_differentiableAt h, smul_zero]
           apply deriv_zero_of_not_differentiableAt
           intro h'
           apply h
           have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =
               α⁻¹ • fun t : ℝ => α • f (g * NormedSpace.exp ((t : ℂ) • X)) := by
             funext t
             simp [smul_smul, inv_mul_cancel₀ hα]
           rw [e]
           exact h'.const_smul α⁻¹)
end Formalism.FourierDecayAlt.P5
