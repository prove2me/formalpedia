-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_Phi_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:04.870539+00:00
-- url     : https://prove2.me/submissions/26e4f64d-df7b-47c4-b940-75ac7331c868

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K) {m N : ℕ} (hN : N = m + 1)
  (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K) (c : Kˣ)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (x : Fin N → R) :
    iso_Phi R hN Z ξ (Submodule.Quotient.mk x) = affineForm R hN ξ x := rfl
end Formalism.FourierDecayAlt.P.A5x8
