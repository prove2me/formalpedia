-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.kap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:20.908359+00:00
-- url     : https://prove2.me/submissions/f31bc65b-c5b9-46b1-8562-194885717e89

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_kap_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_reg_left

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
variable {K S : Type} [Field K]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution (q : K → K) (w : List (Letter K S)) :
    ∀ L : List (Letter K S), DualOK q w L → kap q w L = kapF q w L
  | [], _ => rfl
  | l :: L, h => by
    obtain ⟨h1, h2, h3⟩ := h
    rw [kap, kapF, mul_div_assoc, kap_step q w l L (reg_left h1) h2, solution q w L h3, mul_assoc]
    rfl
end Formalism.FourierDecayAlt.P.Wd10
