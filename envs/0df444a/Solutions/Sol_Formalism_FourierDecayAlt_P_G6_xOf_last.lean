-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G6.xOf_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:00.22581+00:00
-- url     : https://prove2.me/submissions/b4327f45-b520-4479-b2ef-8c043a7d4530

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_blk_cl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G6
theorem _root_.solution {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (B : Fin (m + 1) → ℂ) :
    xOf X B (Fin.last m) = B (Fin.last m) := by
  rw [xOf, Fin.succ_last, blk_cl]
end Formalism.FourierDecayAlt.P.G6
