-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.b_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:21.221242+00:00
-- url     : https://prove2.me/submissions/711dbbb0-ed18-4855-801c-2a45294032df

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_psi_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_psi_q_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_q_inv
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
variable {M : Matrix (Fin m) (Fin m) K}
variable {L Λ : AddSubgroup K}
variable {ψ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    {x l : Fin m → K} (hx : x ∈ PL L m) (hl : l ∈ PL Λ m) : ψ (x ⬝ᵥ M *ᵥ l) = 1 := by
  have h1 := q_inv hInv hx hl
  have h0 := q_inv hInv (PL L m).zero_mem hl
  rw [zero_add] at h0
  rw [psi_q_add ψ h2 hM, h0] at h1
  simp only [mulVec_zero, dotProduct_zero, mul_zero, AddChar.map_zero_eq_one, mul_one] at h1
  exact mul_left_cancel₀ (psi_ne_zero ψ _) (h1.trans (mul_one _).symm)
end Formalism.FourierDecayAlt.P.A6x6
