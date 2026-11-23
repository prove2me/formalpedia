-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.mem_range_iC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:54.873329+00:00
-- url     : https://prove2.me/submissions/22077622-e877-42ff-a60c-b6b85aead502

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_mk_outV
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_rowFun_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_rowFun_kills


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
theorem _root_.solution (Z : Matrix (Fin m) (Fin m) K) (hd : IsUnit Z.det) (x : Fin m → KR R)
    (hx : ∀ j, (Z *ᵥ outV R x) j ∈ R) : x ∈ Set.range (iC R Z) := by
  let b : Fin m → R := fun j => ⟨_, hx j⟩
  have hb : coeLin R b = Z *ᵥ outV R x := by
    funext j; rw [P.coeLin_apply]
  refine ⟨Submodule.Quotient.mk b, ?_⟩
  funext j
  have h1 : iC R Z (Submodule.Quotient.mk b) j =
      (latZ R Z).liftQ (A5x3.rowFun R Z j) (A5x3.rowFun_kills R Z hd j)
        (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk b : coker R Z))) := rfl
  have h2 : (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk b : coker R Z)) :
      coker R Z) = Submodule.Quotient.mk b := Quotient.out_eq _
  rw [h1, h2, Submodule.liftQ_apply, A5x3.rowFun_apply, hb, mulVec_mulVec,
    Matrix.nonsing_inv_mul Z hd, one_mulVec, mk_outV]
end Formalism.FourierDecayAlt.P.A5x8
