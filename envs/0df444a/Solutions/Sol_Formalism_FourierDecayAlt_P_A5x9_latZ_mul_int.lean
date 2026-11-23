-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.latZ_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:16.108808+00:00
-- url     : https://prove2.me/submissions/73d48783-d563-4917-9356-b93db5c4f9f1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_up
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_inv
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_liftR_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z g : Matrix (Fin n) (Fin n) K) (hg : IsUpUni g) (hi : IsInt R g) :
    latZ R (Z * g) = latZ R Z := by
  ext x
  rw [mem_latZ, mem_latZ]
  constructor
  · rintro ⟨t, e⟩
    refine ⟨liftR R g hi *ᵥ t, ?_⟩
    rw [coeLin_mulVec, liftR_map, Matrix.mulVec_mulVec]; exact e
  · rintro ⟨t, e⟩
    have hi' := isInt_inv R hi (isUpUni_det K hg)
    refine ⟨liftR R g⁻¹ hi' *ᵥ t, ?_⟩
    rw [coeLin_mulVec, liftR_map, Matrix.mulVec_mulVec, Matrix.mul_assoc, mul_inv_one_up hg,
      Matrix.mul_one]
    exact e
end Formalism.FourierDecayAlt.P.A5x9
