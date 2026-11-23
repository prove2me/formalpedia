-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.inv_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:57.092786+00:00
-- url     : https://prove2.me/submissions/ccaa2e37-f6f5-4c41-b1ce-c1cfda43726f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_inv_mem_of_near
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution [TopologicalSpace K] [IsTopologicalRing K] (ho : IsOpen (R : Set K)) (ϖ : Kˣ)
    (hϖ : (ϖ : K) ∈ R) (hu : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (Om : Set K)
    (hOm : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ N : ℕ, ∀ z : Kˣ, (z : K) ∈ Om → (ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K) ∈ R := by
  refine hOm.induction_on
    (p := fun s => ∃ N : ℕ, ∀ z : Kˣ, (z : K) ∈ s → (ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K) ∈ R)
    ?_ ?_ ?_ ?_
  · exact ⟨0, fun z hz => absurd hz (Set.notMem_empty _)⟩
  · rintro s t hst ⟨N, hN⟩
    exact ⟨N, fun z hz => hN z (hst hz)⟩
  · rintro s t ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, fun z hz => ?_⟩
    rcases hz with hz | hz
    · rw [pow_add, mul_comm ((ϖ : K) ^ N), mul_assoc]
      exact R.mul_mem (R.pow_mem hϖ M) (hN z hz)
    · rw [pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem hϖ N) (hM z hz)
  · intro x hx
    obtain ⟨z0, rfl⟩ := hU x hx
    obtain ⟨m, hm⟩ := hu ((z0⁻¹ : Kˣ) : K)
    refine ⟨{z | ((z0⁻¹ : Kˣ) : K) * ((ϖ⁻¹ : Kˣ) : K) * (z - (z0 : K)) ∈ R},
      mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_), m, fun z hz => ?_⟩
    · exact ho.preimage (continuous_const.mul (continuous_id.sub continuous_const))
    · simp [R.zero_mem]
    · have h0 : ((z0⁻¹ : Kˣ) : K) * (z0 : K) = 1 := Units.inv_mul z0
      have h1 : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := Units.mul_inv ϖ
      have h2 := inv_mem_of_near R ϖ hϖ hu (z0⁻¹ * z) _ hz (by
        rw [Units.val_mul]
        linear_combination h0 -
          (((z0⁻¹ : Kˣ) : K) * ((z : K) - (z0 : K))) * h1)
      have e : (ϖ : K) ^ m * ((z⁻¹ : Kˣ) : K) =
          ((ϖ : K) ^ m * ((z0⁻¹ : Kˣ) : K)) * (((z0⁻¹ * z)⁻¹ : Kˣ) : K) := by
        rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
        linear_combination (-(ϖ : K) ^ m * ((z⁻¹ : Kˣ) : K)) * h0
      rw [e]
      exact R.mul_mem hm h2
end Formalism.FourierDecayAlt.P.KernelScalingBack
