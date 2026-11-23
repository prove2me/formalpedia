-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.coordU_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:27.181121+00:00
-- url     : https://prove2.me/submissions/eab09237-22ce-4701-b5f4-39ab17bb8154

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_joinU_idx

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    coordU (blk A b a e) = joinU (coordU A, b) := by
  funext p
  obtain ⟨s, rfl⟩ := (idxEquiv n).surjective p
  rw [joinU_idx]
  rcases s with ⟨⟨i, j⟩, h⟩ | i
  · exact blk_cc A b a e i j
  · exact blk_cl A b a e i
end Formalism.FourierDecayAlt.P.G5
