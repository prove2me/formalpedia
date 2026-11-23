-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_bigZ_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:38.090615+00:00
-- url     : https://prove2.me/submissions/5cc676d1-b000-48f7-8ed2-08fc770011cf

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
variable {K : Type} [CommRing K] {m N : ℕ} (hN : N = m + 1)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K)
    (c : Kˣ) : (bigZ hN Z ξ η (c : K))⁻¹ =
      blkM hN (Z⁻¹ + vecMulVec η (((c⁻¹ : Kˣ) : K) • ξ)) (-(((c⁻¹ : Kˣ) : K) • η))
        (-(((c⁻¹ : Kˣ) : K) • ξ)) ((c⁻¹ : Kˣ) : K) := by
  exact Matrix.inv_eq_right_inv (iso_bigZ_mul_inv hN Z hZ ξ η c)
end Formalism.FourierDecayAlt.P.A5x8
