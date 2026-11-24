-- Prove2me | solution 1 for Formalism.ResultantValuation.AdjugateJacobi.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:28.907549+00:00
-- url     : https://prove2.me/submissions/96670f54-9a19-4c68-b405-c50a9d4a3190

import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate
import Theorems.Thm_Formalism_ResultantValuation_AdjugateJacobi_det_twoCol
import Theorems.Thm_Formalism_ResultantValuation_AdjugateJacobi_mulVec_adjugate_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.AdjugateJacobi
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.ResultantValuation.AdjugateJacobi
theorem _root_.solution (M : Matrix n n R) {k i : n} (hki : k ≠ i) (l j : n) :
    M.det * minorF M k i l j = M.det * (M.det * minorQ M k i l j) := by
  have hN : (twoCol k i (fun r => M.adjugate r l) (fun r => M.adjugate r j)).det =
      minorF M k i l j := by
    rw [det_twoCol hki, minorF]
  have hMN : M * twoCol k i (fun r => M.adjugate r l) (fun r => M.adjugate r j) =
      ((M.updateCol i (M.det • Pi.single j 1)).updateCol k (M.det • Pi.single l 1)) := by
    rw [twoCol, mul_updateCol, mul_updateCol, mul_one, mulVec_adjugate_col,
      mulVec_adjugate_col, updateCol_comm _ hki]
  have := congrArg det hMN
  rw [det_mul, hN, det_updateCol_smul, updateCol_comm _ (Ne.symm hki), det_updateCol_smul,
    updateCol_comm _ hki] at this
  rw [this, minorQ]
end Formalism.ResultantValuation.AdjugateJacobi
