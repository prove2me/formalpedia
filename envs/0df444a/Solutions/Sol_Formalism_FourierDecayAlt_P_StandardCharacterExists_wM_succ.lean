-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.wM_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:34.844203+00:00
-- url     : https://prove2.me/submissions/03936370-9ad3-4622-8897-36801405c0d1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wMat_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wMat_mulVec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) (i : Fin n)
    (j : Fin (n + 1)) :
    (wMat (n + 1) * Mcoord 0 X B ρ σ) i.succ j = blk X B 0 0 i.castSucc j := by
  rw [wMat_mul_apply, Fin.rev_succ, Mcoord]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [blk_cl, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
  · rw [blk_cc, blk_cc, wMat_mul_apply, Fin.rev_rev]; simp
end Formalism.FourierDecayAlt.P.StandardCharacterExists
