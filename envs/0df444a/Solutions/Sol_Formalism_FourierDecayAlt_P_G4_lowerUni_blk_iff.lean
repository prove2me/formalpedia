-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.lowerUni_blk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:59.970349+00:00
-- url     : https://prove2.me/submissions/64ea9b98-4504-4db6-b53f-7d90571a9347

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_blk_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    IsLowerUni (blk A b a e) ↔ IsLowerUni A ∧ b = 0 ∧ e = 1 := by
  unfold IsLowerUni
  rw [blk_transpose, upperUni_blk_iff]
end Formalism.FourierDecayAlt.P.G4
