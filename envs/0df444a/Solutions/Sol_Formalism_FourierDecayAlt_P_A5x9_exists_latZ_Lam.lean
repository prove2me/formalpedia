-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.exists_latZ_Lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:44.032868+00:00
-- url     : https://prove2.me/submissions/6565d08a-d294-4a7e-85ad-503880f968a7

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_lower_right_block_is_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_msk_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_msk_msk
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x9_Lam_mul__36cdfb417c73
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mat_det_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mat_Lam_mulVec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_up
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
theorem _root_.solution (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (hZ : IsInt R (Z₀ * p)) (r : Fin n → K) (hr : ∀ j, r j ∈ R) (hr0 : msk k r = r) :
    ∃ z ∈ latZ R (Z₀ * p), abelian₂ R k Z₀ z = r := by
  have ht := isD_mulVec_int R k (lower_right_block_is_diagonal R k hp.2) hr
  let t : Fin n → R := fun j => ⟨_, ht j⟩
  have et : coeLin R t = b22 k p⁻¹ *ᵥ r := by
    funext j; rw [coeLin_apply]
  let z : Fin n → R := liftR R (Z₀ * p) hZ *ᵥ t
  have ez : (Z₀ * p) *ᵥ coeLin R t = coeLin R z := by rw [coeLin_mulVec, liftR_map]
  refine ⟨z, (mem_latZ R _ z).2 ⟨t, ez⟩, ?_⟩
  rw [Lam_mul' R k Z₀ p hp, mat_Lam_mulVec R k _ (mat_det_mul R k Z₀ p hd hp) z t ez, et]
  conv_lhs => rw [← hr0]
  rw [← msk_mulVec k hp.2.1, msk_msk, ← msk_mulVec k hp.1.1, Matrix.mulVec_mulVec,
    mul_inv_one_up hp.1.1, Matrix.one_mulVec, hr0]
end Formalism.FourierDecayAlt.P.A5x9
