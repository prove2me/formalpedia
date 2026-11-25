-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.tendsto_singS_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:15.212595+00:00
-- url     : https://prove2.me/submissions/90335b1a-aef4-42ab-a77e-731ac9b2c6e2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumBoxIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSingSSum
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_coe_filter_box
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_dominated
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_absNorm_bId
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_bId_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_bId_sup_eq_top
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_boxSet_finite
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_ne_zero_of_mem_boxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prod_aLoc
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_roL_diff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_roL_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_singS_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_summable_inv_absNorm_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_tendsto_weighted_tprod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_ne_zero_of_mem_boxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_two_le_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finite_vd_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_tendsto_sum_box_ideal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_two_le_absNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open A5
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * singS F h L n)
      atTop (𝓝 ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V))) := by
  classical
  set S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    (finite_vd_ne_zero (F := F) hK hF hs hd hL hLi).toFinset with hSdef
  have hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S := fun 𝔭 h𝔭 =>
    (Set.Finite.mem_toFinset _).mpr h𝔭
  obtain ⟨C, hC⟩ := dominated hK hF hs hd hL hLi hm S
  set c0 : ℝ := (finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
    Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) with hc0
  have main := tendsto_weighted_tprod
    (q := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ))
    (fun 𝔭 => by exact_mod_cast two_le_absNorm 𝔭.2) summable_inv_absNorm_sq S
    (ρ := roL h L S) (roL_zero hK hF hs hd hL hLi hm hS) (fun 𝔭 h𝔭 j => by simp [roL, h𝔭])
    (roL_diff hK hF hs hd hL hLi hm hS) valF
    (fun j : ℕ => (boxSet_finite hK hF ((j : ℝ) ^ 2)).toFinset)
    (fun n => (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n)
    (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)))
    (c0 * ∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹) c0 C
    (fun 𝔭 => (eFac K (finrank K V) 𝔭.1)⁻¹) (fun h0 => by rw [h0, zero_mul]) ?_ ?_ ?_
  · refine main.congr fun j => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (boxSet_finite hK hF ((j : ℝ) ^ 2))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb : n ∈ boxSet K F ((j : ℝ) ^ 2) := (Set.Finite.mem_toFinset _).mp hn
    rw [singS_eq hK hF hs hd hL hLi hm hS (ne_zero_of_mem_boxSet hb), mul_assoc]
  · intro v hv
    have ht := tendsto_sum_box_ideal hK hF hs hd hL hLi hm S hS (bId_ne_bot v)
      (fun 𝔭 h𝔭 => bId_sup_eq_top (Finset.disjoint_right.mp hv h𝔭))
    simp_rw [coe_filter_box hK hF, finsum_mem_coe_finset] at ht
    rw [absNorm_bId] at ht
    have he : c0 * (∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹) /
        nrm (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ)) v =
        c0 / nrm (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ)) v *
          ∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹ := by ring
    rw [he]
    exact ht
  · filter_upwards [eventually_ge_atTop 1] with j hj v
    refine hC _ ?_ v
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith
  · intro S' hS'
    have ht := tendsto_sum_box_ideal hK hF hs hd hL hLi hm S' (fun 𝔭 h𝔭 => hS' (hS 𝔭 h𝔭))
      (b := ⊤) (by simp) (fun 𝔭 _ => by simp)
    simp only [Submodule.mem_top, and_true, Ideal.absNorm_top, Nat.cast_one, div_one] at ht
    refine ht.congr fun j => ?_
    have hset : {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2)} = boxSet K F ((j : ℝ) ^ 2) := rfl
    rw [hset, finsum_mem_eq_finite_toFinset_sum _ (boxSet_finite hK hF ((j : ℝ) ^ 2))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb : n ∈ boxSet K F ((j : ℝ) ^ 2) := (Set.Finite.mem_toFinset _).mp hn
    rw [mul_assoc, ← prod_aLoc hK hF hs hd hL hLi hS hS' (ne_zero_of_mem_boxSet hb)]
    rfl
end Formalism.HermitianLattices.Ext.L3
