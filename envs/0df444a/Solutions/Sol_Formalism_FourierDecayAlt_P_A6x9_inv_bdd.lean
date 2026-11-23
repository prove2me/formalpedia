-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.inv_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:22:41.09375+00:00
-- url     : https://prove2.me/submissions/9f9ed74c-0efa-42f3-9878-e906929b9ffe

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_J_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_one_add_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_pow_mem_mono
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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {C : Set K} (hC : IsCompact C)
    (hU : ∀ z ∈ C, IsUnit z) : ∃ k : ℕ, ∀ z ∈ C, ∀ zi : K, z * zi = 1 → (π : K) ^ k * zi ∈ R := by
  obtain ⟨k, hk⟩ := hC.elim_directed_cover
    (fun k : ℕ => {z | ∃ zi : K, z * zi = 1 ∧ (π : K) ^ k * zi ∈ R})
    (fun k => by
      rw [isOpen_iff_mem_nhds]
      rintro z0 ⟨zi0, h0, h1⟩
      have hnb : (fun z => zi0 * (z - z0)) ⁻¹' (mulR R ((π : K) ^ 1) : Set K) ∈ 𝓝 z0 := by
        apply (show Continuous fun z => zi0 * (z - z0) by fun_prop).continuousAt.preimage_mem_nhds
        simpa using J_nhds π hd 1
      filter_upwards [hnb] with z hz
      obtain ⟨u, hu, hu2⟩ := one_add_unit π hd hn hπ hπ' _ hz
      refine ⟨zi0 * u, ?_, ?_⟩
      · have hu2 : (1 + zi0 * (z - z0)) * u = 1 := hu2
        linear_combination hu2 + u * h0
      · rw [← mul_assoc]; exact R.mul_mem h1 hu)
    (fun z hz => by
      obtain ⟨u, rfl⟩ := hU z hz
      obtain ⟨k, hk⟩ := hπ' ((u⁻¹ : Kˣ) : K)
      exact Set.mem_iUnion.2 ⟨k, _, by simp, hk⟩)
    (directed_of_isDirected_le (fun i j hij z hz => by
      obtain ⟨zi, h0, h1⟩ := hz
      exact ⟨zi, h0, pow_mem_mono π hπ hij h1⟩))
  refine ⟨k, fun z hz zi hzi => ?_⟩
  obtain ⟨zi', h0, h1⟩ := hk hz
  have : zi = zi' := by linear_combination zi' * hzi - zi * h0
  rwa [this]
end Formalism.FourierDecayAlt.P.A6x9
