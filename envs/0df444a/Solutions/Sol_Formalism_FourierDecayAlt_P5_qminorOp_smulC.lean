-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.qminorOp_smulC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:09:43.936395+00:00
-- url     : https://prove2.me/submissions/041b10dc-40aa-4e5d-8d96-9442c77a850d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
import Theorems.Thm_Formalism_FourierDecayAlt_P5_top_smulC
import Theorems.Thm_Formalism_FourierDecayAlt_P5_foldr_smulC
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
theorem _root_.solution {t : ℕ}
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    (hE : ∀ a b, SmulC (Eop a b)) (a b : Fin t → Fin n) (u : ℂ) : SmulC (qminorOp Eop a b u) := by
  intro α f
  simp only [qminorOp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hT : (List.ofFn fun k : Fin t => Formalism.QuantumDeterminants.Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) (α • f) =
      α • (List.ofFn fun k : Fin t => Formalism.QuantumDeterminants.Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f :=
    foldr_smulC (List.ofFn fun k : Fin t => Formalism.QuantumDeterminants.Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k))
      (fun T hT => by
        simp only [List.mem_ofFn, Set.mem_range] at hT
        obtain ⟨k, rfl⟩ := hT
        exact top_smulC hE _ _ _) α f
  rw [hT, smul_comm]
end Formalism.FourierDecayAlt.P5
