-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.opL_fsv_smul_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:49.815409+00:00
-- url     : https://prove2.me/submissions/2c99c89c-6c12-4862-b33e-9be34feec3b5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
import Theorems.Thm_Formalism_FourierDecayAlt_P5_wirt_fsv_smul_other
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
theorem _root_.solution (t : ℂ) {l l' : Fin m} (hl : l' ≠ l) (i : Fin 6) (φ : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) :
    opL l' i (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • opL l' i φ c := by
  match i with
  | 0 =>
    show Formalism.QuantumDeterminants.pOp l' _ c = _ • Formalism.QuantumDeterminants.pOp l' φ c
    simp only [Formalism.QuantumDeterminants.pOp]
    split_ifs with h
    · rw [(wirt_fsv_smul_other t hl φ c (hd h)).1, smul_comm]
    · rw [smul_zero]
  | 1 => exact smul_comm _ _ _
  | 2 => exact smul_comm _ _ _
  | 3 =>
    show Formalism.QuantumDeterminants.pbOp l' _ c = _ • Formalism.QuantumDeterminants.pbOp l' φ c
    simp only [Formalism.QuantumDeterminants.pbOp]
    split_ifs with h
    · rw [(wirt_fsv_smul_other t hl φ c (hd h)).2, smul_comm]
    · rw [smul_zero]
  | 4 => exact smul_comm _ _ _
  | 5 => exact smul_comm _ _ _
end Formalism.FourierDecayAlt.P5
