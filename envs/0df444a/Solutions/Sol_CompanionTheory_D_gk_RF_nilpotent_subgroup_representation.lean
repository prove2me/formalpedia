-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.nilpotent_subgroup_representation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:00:51.153829+00:00
-- url     : https://prove2.me/submissions/bdad52b4-253d-451a-9883-267345c405ce

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_lowers_of_Z
import Theorems.Thm_CompanionTheory_D_gk_RF_xw_mulVec
import Theorems.Thm_CompanionTheory_D_gk_RF_skew_xw
import Theorems.Thm_CompanionTheory_D_gk_RF_perp_symm
import Theorems.Thm_CompanionTheory_D_gk_RF_rep_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
namespace CompanionTheory.D.gk.RF
theorem _root_.solution : NilpRep := by
  intro K _ _ _ n J W hJ hd hW d w hs
  have hwW : ∀ k, w k ∈ W := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have sk : ∀ b : Fin d → Fin n → K, (∑ i, xw J (w i) (b i))ᴴ * J + J * ∑ i, xw J (w i) (b i) = 0 := fun b => by
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => skew_xw hJ _ _
  refine ⟨fun b hb => ⟨sk b, fun z hz => ?_, fun z hz => ?_, fun z => ?_⟩, fun b hb => ⟨sk b, fun z hz => ?_,
    fun z => ?_⟩, fun X hX => ?_, fun X hX => ?_⟩
  · rw [sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => by
      rw [xw_mulVec, perp_symm hJ (hb i) hz, hW hz _ (hwW i), zero_smul, zero_smul, sub_zero]
  · rw [sum_mulVec]
    exact W.sum_mem fun i _ => by
      rw [xw_mulVec, hz _ (hwW i), zero_smul, sub_zero]; exact W.smul_mem _ (hwW i)
  · rw [sum_mulVec]
    exact (perp J W).sum_mem fun i _ => by
      rw [xw_mulVec]
      exact (perp J W).sub_mem ((perp J W).smul_mem _ (hW (hwW i))) ((perp J W).smul_mem _ (hb i))
  · rw [sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => by
      rw [xw_mulVec, hz _ (hwW i), hz _ (hb i), zero_smul, zero_smul, sub_zero]
  · rw [sum_mulVec]
    exact W.sum_mem fun i _ => by
      rw [xw_mulVec]; exact W.sub_mem (W.smul_mem _ (hwW i)) (W.smul_mem _ (hb i))
  · obtain ⟨b, h1, -, h3⟩ := rep_span hJ hd hW hs hX
    exact ⟨b, h1, h3⟩
  · obtain ⟨b, -, h2, h3⟩ := rep_span hJ hd hW hs ⟨hX.1, lowers_of_Z hW hX.2.1 hX.2.2⟩
    exact ⟨b, h2 hX.2.2, h3⟩
end CompanionTheory.D.gk.RF
