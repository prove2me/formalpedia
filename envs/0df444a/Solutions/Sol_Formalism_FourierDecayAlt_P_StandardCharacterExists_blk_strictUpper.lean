-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.blk_strictUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:01.521971+00:00
-- url     : https://prove2.me/submissions/01bedd63-09a9-485a-a3d2-f5a7f3e48c83

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_blk_ll

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
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → ℂ) (hX : IsStrictUpper X) :
    IsStrictUpper (blk X B 0 0) := by
  intro i j hji
  refine Fin.lastCases ?_ (fun i => ?_) i hji
  · intro _
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [blk_ll]
    · rw [blk_lc]; rfl
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h
      exact absurd h (not_le.mpr (Fin.castSucc_lt_last i))
    · intro h
      rw [blk_cc]
      exact hX i j (by simpa using h)
end Formalism.FourierDecayAlt.P.StandardCharacterExists
