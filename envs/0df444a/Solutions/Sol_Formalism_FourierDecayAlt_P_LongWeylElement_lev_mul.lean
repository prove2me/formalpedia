-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.lev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:21.739816+00:00
-- url     : https://prove2.me/submissions/233cb5e8-eea3-446d-a3d8-97926026b68f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (k r' : ℕ) (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  first
    | exact Formalism.FourierDecayAlt.P.B2x2.lev_mul k r' g h
    | exact (Formalism.FourierDecayAlt.P.B2x5.lev_mul k r' g h).symm
end Formalism.FourierDecayAlt.P.LongWeylElement
