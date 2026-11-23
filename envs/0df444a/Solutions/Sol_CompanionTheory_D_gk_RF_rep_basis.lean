-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.rep_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:31.350898+00:00
-- url     : https://prove2.me/submissions/959acd97-5995-49e6-a6c1-2af61119109b

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_mat_extC
import Theorems.Thm_CompanionTheory_D_gk_RF_star_half
import Theorems.Thm_CompanionTheory_D_gk_RF_xw_mulVec
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_star
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_sub_right
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_smul_right
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_sum_right
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_add_leftC
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_neg_left
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_smul_leftC
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_sum_left
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_skew
import Theorems.Thm_CompanionTheory_D_gk_RF_mem_perp_spanC
import Theorems.Thm_CompanionTheory_D_gk_RF_exists_dual

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
theorem _root_.solution [CharZero K] (hJ : Jᴴ = J) (hd : IsUnit J.det) (hW : Isot J W) {κ : Type} [Fintype κ]
    [DecidableEq κ] {v : κ → Fin n → K} (hv : LinearIndependent K v) (hs : Submodule.span K (Set.range v) = W)
    {X : Matrix (Fin n) (Fin n) K} (hX : InL J W X) :
    ∃ b : κ → Fin n → K, (∀ k, b k ∈ perp J W) ∧ ((∀ z, X *ᵥ z ∈ W) → ∀ k, b k ∈ W) ∧ X = ∑ k, xw J (v k) (b k) := by
  obtain ⟨u, hu⟩ := exists_dual hJ hd hv
  have hu' : ∀ i j, hf J (v i) (u j) = if i = j then 1 else 0 := fun i j => by
    rw [← hf_star hJ, hu]; by_cases h : i = j <;> simp [h, eq_comm]
  have hvW : ∀ k, v k ∈ W := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have hexp : ∀ w ∈ W, ∑ i, hf J (u i) w • v i = w := by
    intro w hw
    rw [← hs] at hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
    simp only [hf_sum_right, hf_smul_right, hu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  let s : κ → κ → K := fun i k => hf J (u i) (X *ᵥ u k)
  have hss : ∀ i k, star (s k i) = -s i k := fun i k => by
    simp only [s]; rw [hf_star hJ, hf_skew hX.1]
  let b : κ → Fin n → K := fun k => -(X *ᵥ u k) + ∑ i, ((2 : K)⁻¹ * s i k) • v i
  have hsum : ∀ k, ∑ i, ((2 : K)⁻¹ * s i k) • v i ∈ W := fun k =>
    W.sum_mem fun i _ => W.smul_mem _ (hvW i)
  refine ⟨b, fun k => (perp J W).add_mem ((perp J W).neg_mem (hX.2.2.2 _)) (hW (hsum k)),
    fun h k => W.add_mem (W.neg_mem (h _)) (hsum k), ?_⟩
  have e1 : ∀ z ∈ perp J W, (∑ k, xw J (v k) (b k)) *ᵥ z = X *ᵥ z := fun z hz => by
    rw [sum_mulVec, ← hexp _ (hX.2.2.1 z hz)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [xw_mulVec, hz _ (hvW k), zero_smul, sub_zero]
    simp only [b]
    rw [hf_add_leftC, hz _ (hsum k), add_zero, hf_neg_left, hf_skew hX.1, neg_neg]
  have e2 : ∀ j, (∑ k, xw J (v k) (b k)) *ᵥ u j = X *ᵥ u j := fun j => by
    have hb : ∀ k, hf J (b k) (u j) = (2 : K)⁻¹ * s k j := fun k => by
      simp only [b]
      rw [hf_add_leftC, hf_neg_left, hf_skew hX.1, neg_neg, hf_sum_left]
      simp only [hf_smul_leftC, hu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        star_mul', star_half, hss]
      show s k j + _ = _
      ring
    rw [sum_mulVec]
    simp only [xw_mulVec, hb, hu', ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp only [b]
    abel
  refine mat_extC fun z => ?_
  have hz : z - ∑ j, hf J (v j) z • u j ∈ perp J W := by
    rw [← hs]
    refine mem_perp_spanC fun i => ?_
    simp only [hf_sub_right, hf_sum_right, hf_smul_right, hu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]
  rw [← sub_add_cancel z (∑ j, hf J (v j) z • u j), mulVec_add, mulVec_add, e1 _ hz, mulVec_sum, mulVec_sum]
  simp only [mulVec_smul, e2]
end CompanionTheory.D.gk.RF
