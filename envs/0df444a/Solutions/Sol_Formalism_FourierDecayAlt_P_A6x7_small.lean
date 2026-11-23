-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:42.813687+00:00
-- url     : https://prove2.me/submissions/810dd2e6-4ca3-4e4a-ba3e-b29d0d3001be

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_eq_zero_of_ideal
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7
theorem _root_.solution (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {ϖ : Kˣ}
    (hϖ : (ϖ : K) ∈ R) (hϖ' : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (V : Set K)
    (hV : V ∈ 𝓝 (0 : K)) : ∃ n : ℕ, ∀ r ∈ R, (ϖ : K) ^ n * r ∈ V := by
  have := hD.t2
  have hcl : ∀ n : ℕ, IsClosed ((fun r => (ϖ : K) ^ n * r) '' (R : Set K)) := fun n =>
    (hD.isCompact.image (continuous_const.mul continuous_id)).isClosed
  have hC : IsCompact ((R : Set K) \ interior V) := hD.isCompact.diff isOpen_interior
  obtain ⟨n, hn⟩ := hC.elim_directed_cover
    (fun n : ℕ => ((fun r => (ϖ : K) ^ n * r) '' (R : Set K))ᶜ) (fun n => (hcl n).isOpen_compl)
    (by
      intro y hy
      rw [Set.mem_iUnion]
      by_contra hcon
      push Not at hcon
      have hy0 : y = 0 := by
        apply eq_zero_of_ideal hD h0
        intro z
        obtain ⟨m, hm⟩ := hϖ' z
        have := hcon m
        rw [Set.notMem_compl_iff] at this
        obtain ⟨r, hr, rfl⟩ := this
        have e : (ϖ : K) ^ m * r * z = r * ((ϖ : K) ^ m * z) := by ring
        show (ϖ : K) ^ m * r * z ∈ R
        rw [e]; exact R.mul_mem hr hm
      exact hy.2 (hy0 ▸ mem_interior_iff_mem_nhds.2 hV))
    (by
      apply directed_of_isDirected_le
      intro a b hab
      apply Set.compl_subset_compl.2
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      exact ⟨(ϖ : K) ^ k * r, R.mul_mem (R.pow_mem hϖ k) hr, by simp only [pow_add]; ring⟩)
  refine ⟨n, fun r hr => ?_⟩
  by_contra hcon
  have h1 : (ϖ : K) ^ n * r ∈ (R : Set K) \ interior V :=
    ⟨R.mul_mem (R.pow_mem hϖ n) hr, fun h => hcon (interior_subset h)⟩
  exact hn h1 ⟨r, hr, rfl⟩
end Formalism.FourierDecayAlt.P.A6x7
