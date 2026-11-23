-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.upper_joinU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:14.701885+00:00
-- url     : https://prove2.me/submissions/64b52228-22ab-4333-a060-e9cbcb32ad4d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_coordU_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_coordU_blk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {n : ℕ} (v : UT n → ℂ) (b : Fin n → ℂ) : upper (joinU (v, b)) = blk (upper v) b 0 1 := by
  have hj : joinU (v, b) = coordU (blk (upper v) b 0 1) := by rw [coordU_blk, coordU_upper]
  rw [hj]
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [upper, strictUpper, blk_ll]
    | cast j =>
      have h1 : ¬ (Fin.last n < j.castSucc) := not_lt.2 (Fin.castSucc_lt_last j).le
      simp [upper, strictUpper, blk_lc, h1, (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [upper, strictUpper, coordU, blk_cl, Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne]
    | cast j =>
      by_cases h : i < j
      · simp [upper, strictUpper, coordU, blk_cc, h, h.ne]
      · simp [upper, strictUpper, coordU, blk_cc, h, Matrix.one_apply]
end Formalism.FourierDecayAlt.P.G5
