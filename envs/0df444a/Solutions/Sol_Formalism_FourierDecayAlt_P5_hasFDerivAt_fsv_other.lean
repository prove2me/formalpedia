-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.hasFDerivAt_fsv_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:01.697234+00:00
-- url     : https://prove2.me/submissions/cd190adb-3726-4a53-b162-9869783ccd8e

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
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (t : ℂ) (l : Fin m) (c : Fin m → ℂ) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℂ, HasFDerivAt (fun c' : Fin m → ℂ => fsv t (c' l)) D c ∧
      ∀ l' : Fin m, l' ≠ l → ∀ v : ℂ, D (Pi.single l' v) = 0 := by
  have hconj : Differentiable ℝ (fun z : ℂ => conj z) := Complex.conjCLE.differentiable
  have hlin : Differentiable ℝ (fun z : ℂ => t * z - conj t * conj z) := by
    first
      | fun_prop
      | (apply Differentiable.sub
         · exact (differentiable_id (𝕜 := ℝ) (E := ℂ)).const_mul t
         · exact hconj.const_mul (conj t))
  have hg : DifferentiableAt ℝ (fun z : ℂ => fsv t z) (c l) := by
    unfold fsv
    first
      | exact ((Complex.differentiable_exp (𝕜 := ℝ)).comp hlin) (c l)
      | exact (hlin (c l)).cexp
      | fun_prop
  refine ⟨(fderiv ℝ (fun z : ℂ => fsv t z) (c l)).comp (ContinuousLinearMap.proj l), ?_, ?_⟩
  · have h := hg.hasFDerivAt.comp c (hasFDerivAt_apply (𝕜 := ℝ) l c)
    exact h
  · intro l' hl' v
    simp [Pi.single_apply, Ne.symm hl']
end Formalism.FourierDecayAlt.P5
