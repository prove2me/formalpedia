-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.lev_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:04.336812+00:00
-- url     : https://prove2.me/submissions/15483992-76ae-482e-8b3a-bc2257735f63

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mm


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution {g h : Mat k r'} (e : ιLev k 1 r' g = ιLev k 1 r' h) : g = h := by
  ext s t
  have := congrFun (congrFun e (levPos k 1 r' s)) (levPos k 1 r' t)
  rwa [lev_mm, lev_mm] at this
end Formalism.FourierDecayAlt.P.LongWeylElement
