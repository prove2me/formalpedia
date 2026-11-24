-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.diagScalar_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:22.722632+00:00
-- url     : https://prove2.me/submissions/04cf4bcb-a878-49dd-8aca-4c2124b3c29f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_diagScalar_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_d0_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_diagScalar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (L : List (SlopeTestRemainingChoices S A)) : d0 L.prod = (L.map d0).prod := by
  induction L with
  | nil => simp [d0_one]
  | cons M L ih => simp [diagScalar_mul, ih]
end Formalism.FourierDecayAlt.P.Wd8
