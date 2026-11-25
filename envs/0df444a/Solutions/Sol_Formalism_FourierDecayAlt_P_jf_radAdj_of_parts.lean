-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_radAdj_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:37:37.524055+00:00
-- url     : https://prove2.me/submissions/b3814f9a-93e0-43bc-a121-aa0b16e1983d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Theorems.Thm_Formalism_FourierDecayAlt_P_compact_support_finite_class
import Theorems.Thm_Formalism_FourierDecayAlt_P_radial_adjoint_of_parts
import Theorems.Thm_Formalism_FourierDecayAlt_P_theta_conj_of_parts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.P.JFxG.BetaAdjC → Formalism.FourierDecayAlt.JF.RadAdj := by
  intro hE hJ hA hB
  exact radial_adjoint_of_parts hE (theta_conj_of_parts hJ compact_support_finite_class hA) hB
end Formalism.FourierDecayAlt.P
