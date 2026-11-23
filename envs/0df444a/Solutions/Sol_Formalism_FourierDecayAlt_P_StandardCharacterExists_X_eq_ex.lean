-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.X_eq_ex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:01.423781+00:00
-- url     : https://prove2.me/submissions/610207aa-c65b-43cd-8386-9cd0276302c9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_ex_fin

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
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) (i k : Fin n) :
    X i k = ex (blk X B 0 0) i k := by
  have := ex_fin (blk X B 0 0) i.castSucc k.castSucc
  rw [blk_cc] at this
  simpa using this.symm
end Formalism.FourierDecayAlt.P.StandardCharacterExists
