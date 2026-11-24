-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.kap_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:01.55511+00:00
-- url     : https://prove2.me/submissions/d22c58d3-3e0d-4105-9a13-3525b1411a53

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_qw_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_ph_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_fac_eq

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
theorem _root_.solution (q : K → K) (w : List (Letter K S)) (l : Letter K S) :
    ∀ L : List (Letter K S), Reg L (dl l).pt → qw q (L ++ w) (ypt l) ≠ 0 →
      qw q (L ++ w) (ypt l) / ph L (dl l).pt = qw q w (ypt l) * (L.map fun l' => fac l l').prod
  | [], _, _ => by simp [ph]
  | l' :: L, hr, hq => by
    have hr1 : RegL l' (dl l).pt := hr l' (by simp)
    have hr2 : Reg L (dl l).pt := fun x hx => hr x (by simp [hx])
    rw [List.cons_append, qw_cons] at hq
    have hq1 := left_ne_zero_of_mul hq
    have hq2 := right_ne_zero_of_mul hq
    rw [List.cons_append, qw_cons, ph_cons, mul_div_mul_comm, solution q w l L hr2 hq1,
      fac_eq l l' hr1 hq2, List.map_cons, List.prod_cons]
    ring
end Formalism.FourierDecayAlt.P.Wd10
