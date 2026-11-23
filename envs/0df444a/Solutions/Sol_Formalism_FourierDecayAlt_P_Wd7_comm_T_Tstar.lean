-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.comm_T_Tstar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:38.571445+00:00
-- url     : https://prove2.me/submissions/2a6c5c62-4169-4f79-b1ac-e7adb665771a

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_commute_Avr_Bvr_of_commute_siteOps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_Tstar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_commute_Avr_Bvr_of_commute_siteOps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (σ : Site A) (hσ : IsSite σ) (Y Y' : K) (i j k l : Fin 2) :
    Commute (Ts σ Y i j) (star (Ts σ Y' k l)) := by
  refine comm_Tstar σ Y' _ (fun x hx => ?_) k l
  refine (commute_Avr_Bvr_of_commute_siteOps σ Y _ (fun y hy => ?_) i j).symm
  exact (hσ.2 y hy x hx).symm
end Formalism.FourierDecayAlt.P.Wd7
