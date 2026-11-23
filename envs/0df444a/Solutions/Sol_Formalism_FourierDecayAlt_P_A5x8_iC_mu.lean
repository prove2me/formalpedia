-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iC_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:57.623805+00:00
-- url     : https://prove2.me/submissions/f9531837-c3a6-441e-aa06-20d21355437a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iC_spec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lastCoord_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_muZ_mk


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
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z) (hd : IsUnit Z.det)
    (β : coker R Z) :
    A5x6.muZ R Z hd β = Submodule.Quotient.mk (lastE (outV R (iC R Z β))) := by
  obtain ⟨b, hb, hβ⟩ := iC_spec R Z hZ hd β
  conv_lhs => rw [← hβ]
  rw [A5x6.muZ_mk, P.lamLin_apply, hb, mulVec_mulVec, Matrix.nonsing_inv_mul Z hd, one_mulVec,
    P.lastCoord_apply]
  rfl
end Formalism.FourierDecayAlt.P.A5x8
