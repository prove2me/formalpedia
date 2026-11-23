-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.wM_zero_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:23.188625+00:00
-- url     : https://prove2.me/submissions/4e653c30-70c2-4c92-9ad0-c7c26aacfbb1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_blk_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_wMat_mul_apply

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
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    (wMat (n + 1) * Mcoord 0 X B ρ σ) 0 (Fin.last n) = σ := by
  rw [wMat_mul_apply, Fin.rev_zero, Mcoord, blk_ll]
end Formalism.FourierDecayAlt.P.StandardCharacterExists
