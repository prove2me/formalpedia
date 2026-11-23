-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.inTT_iff_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:37.273022+00:00
-- url     : https://prove2.me/submissions/4cbe136e-f320-406c-86e6-eb684d0f0902

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_lower_right_block_is_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_inTT_iff

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
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (Z₀ Z₀' p p' : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p)
    (hp' : IsPP R k p') (φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p')) :
    InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ↔ ∃ D, IsD R k D ∧ ∀ v v' : Fin n → R,
      φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        ∀ j, (abelian₂ R k Z₀' v' - D *ᵥ abelian₂ R k Z₀ v) j ∈ R := by
  rw [inTT_iff]
  constructor
  · rintro ⟨D, hD, h⟩
    refine ⟨b22 k p' * D * b22 k p⁻¹,
      isD_mul R k (isD_mul R k (lower_right_block_is_diagonal R k hp'.1) hD) (lower_right_block_is_diagonal R k hp.2), fun v v' hv => ?_⟩
    have e : abelian₂ R k Z₀' v' - (b22 k p' * D * b22 k p⁻¹) *ᵥ abelian₂ R k Z₀ v =
        b22 k p' *ᵥ (abelian₂ R k (Z₀' * p') v' - D *ᵥ abelian₂ R k (Z₀ * p) v) := by
      rw [Matrix.mulVec_sub, ← Lam_mul' R k Z₀' p' hp' v', Lam_mul R k Z₀ p hp v,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e]
    exact isD_mulVec_int R k (lower_right_block_is_diagonal R k hp'.1) (h v v' hv)
  · rintro ⟨D, hD, h⟩
    refine ⟨b22 k p'⁻¹ * D * b22 k p,
      isD_mul R k (isD_mul R k (lower_right_block_is_diagonal R k hp'.2) hD) (lower_right_block_is_diagonal R k hp.1), fun v v' hv => ?_⟩
    have e : abelian₂ R k (Z₀' * p') v' - (b22 k p'⁻¹ * D * b22 k p) *ᵥ abelian₂ R k (Z₀ * p) v =
        b22 k p'⁻¹ *ᵥ (abelian₂ R k Z₀' v' - D *ᵥ abelian₂ R k Z₀ v) := by
      rw [Matrix.mulVec_sub, ← Lam_mul R k Z₀' p' hp' v', Lam_mul' R k Z₀ p hp v,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e]
    exact isD_mulVec_int R k (lower_right_block_is_diagonal R k hp'.2) (h v v' hv)
end Formalism.FourierDecayAlt.P.A5x9
