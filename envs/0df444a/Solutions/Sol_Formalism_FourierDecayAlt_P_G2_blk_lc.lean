-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G2.blk_lc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:03.367972+00:00
-- url     : https://prove2.me/submissions/24205a96-0215-4d34-9d98-4a18a6448153

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_symm_castSucc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_symm_last

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
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G2
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G2
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  simp [blk, symm_castSucc, symm_last]
end Formalism.FourierDecayAlt.P.G2
