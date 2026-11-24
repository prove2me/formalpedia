-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.ph_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:02.698595+00:00
-- url     : https://prove2.me/submissions/da803090-a208-438f-9fd4-6b60b35577f0

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_ph_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_reg_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_hp_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution : ∀ (L : List (Letter K S)) (Y : K), Reg L Y → Reg (L.map dl) Y → ph L Y ≠ 0
  | [], _, _, _ => by simp [ph]
  | l :: L, Y, h1, h2 => by
    rw [ph_cons]
    rw [List.map_cons] at h2
    exact mul_ne_zero (solution L Y (reg_cons h1).2 (reg_cons h2).2) (hp_ne (reg_cons h1).1 (reg_cons h2).1)
end Formalism.FourierDecayAlt.P.Wd10
