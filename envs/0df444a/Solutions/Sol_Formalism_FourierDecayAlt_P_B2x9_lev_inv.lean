-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.lev_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:42:46.533252+00:00
-- url     : https://prove2.me/submissions/60bfd3bb-ee23-4fce-a895-2e5d85295222

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_one


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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (g : Mat k r') (hg : IsUnit g.det) : (ιLev k 1 r' g)⁻¹ = ιLev k 1 r' g⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← lev_mul, Matrix.mul_nonsing_inv _ hg, lev_one]
end Formalism.FourierDecayAlt.P.B2x9
