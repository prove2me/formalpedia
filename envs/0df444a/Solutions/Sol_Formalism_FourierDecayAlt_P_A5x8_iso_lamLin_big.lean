-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iso_lamLin_big
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:20.207194+00:00
-- url     : https://prove2.me/submissions/646d0c81-c16c-4fbb-922c-353a10f03cae

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_bigZ_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_last_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_affine_form_on_vector
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lastCoord_apply


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
include hZ
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (x : Fin N → R) :
    lamLin R (bigZ hN Z ξ η (c : K)) x =
      Submodule.Quotient.mk (((c⁻¹ : Kˣ) : K) * affineForm R hN ξ x) := by
  rw [Formalism.DoubleCosetMeasures.P.lamLin_apply, Formalism.DoubleCosetMeasures.P.lastCoord_apply, iso_last_sum hN, iso_bigZ_inv hN Z hZ,
    ← iso_eta R hN x, iso_coeLin_vec, iso_blkM_mulVec, iso_vec_inr, affine_form_on_vector,
    Submodule.mkQ_apply]
  congr 1
  rw [neg_dotProduct, smul_dotProduct, smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.A5x8
