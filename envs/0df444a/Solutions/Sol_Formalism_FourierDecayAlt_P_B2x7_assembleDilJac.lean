-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.assembleDilJac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:03.396109+00:00
-- url     : https://prove2.me/submissions/6528a341-e3d3-420a-a4ea-ab024836f0d4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dilJacRaw_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dilJacAll_of

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open B2x7
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution : AssembleDilJac := fun hU hN hR _ hE _ _ _ =>
  ⟨dilJacRaw_of hU hN hR hE, dilJacAll_of (dilJacRaw_of hU hN hR hE)⟩
end Formalism.FourierDecayAlt.P.B2x7
