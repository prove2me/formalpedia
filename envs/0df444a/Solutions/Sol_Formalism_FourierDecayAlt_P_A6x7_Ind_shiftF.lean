-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.shiftF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:29.773234+00:00
-- url     : https://prove2.me/submissions/2a35e558-0acd-4994-b5f2-35d3f89f9195

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_qf_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_neg
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Ind
variable {K : Type} [CommRing K] {m : ℕ}
variable {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    (hdet : IsUnit M.det) {L : AddSubgroup K} (y : Fin m → K)
    (hq : ψ (Ring.inverse 2 * (y ⬝ᵥ (M⁻¹ *ᵥ y))) = 1) (hmem : ∀ j, (M⁻¹ *ᵥ y) j ∈ L)
    (ξ : Fin m → K) : gaussF ψ L M (ξ + M⁻¹ *ᵥ y) = ψ (ξ ⬝ᵥ y) * gaussF ψ L M ξ := by
  have hMy : M *ᵥ (M⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  by_cases hx : ∀ i, ξ i ∈ L
  · rw [gaussF_pos hx, gaussF_pos (ξ := ξ + M⁻¹ *ᵥ y) (fun i => L.add_mem (hx i) (hmem i)), qf_add h2 M hM,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hMy]
    have : ψ (qf M (M⁻¹ *ᵥ y)) = 1 := by
      unfold qf; rw [hMy, dotProduct_comm]; exact hq
    rw [this, mul_one, mul_comm]
  · rw [gaussF_neg hx, gaussF_neg, mul_zero]
    intro h
    apply hx
    intro i
    have := L.sub_mem (h i) (hmem i)
    simpa using this
end Formalism.FourierDecayAlt.P.A6x7.Ind
