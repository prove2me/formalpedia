-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.dominated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:04:05.17032+00:00
-- url     : https://prove2.me/submissions/3cefe740-9253-4fc0-be35-31df9801fbbe

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumBoxIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSingSSum
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_coe_filter_box
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_absNorm_bId
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_absNorm_le_of_mem_boxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_bId_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_boxSet_finite
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_ne_zero_of_mem_boxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prodS_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxCube_card_box_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_ne_zero_of_mem_boxSet
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
open Formalism.HermitianLattices.Ext.L3.A5
open scoped Classical
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ,
      |T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n| ≤
        C / nrm (fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℝ)) v := by
  obtain ⟨C1, hC1⟩ := prodS_bound hK hF hs hd hL hLi hm S
  refine ⟨2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1, fun T hT v => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hsum0 : 0 ≤ ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n := by
    refine Finset.sum_nonneg fun n hn => ?_
    have hb : n ∈ boxSet K F T := by
      simpa using (Finset.mem_filter.mp hn).1
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hC1 n (ne_zero_of_mem_boxSet hb)).1
  rw [abs_of_nonneg (mul_nonneg (zpow_nonneg hT0.le _) hsum0)]
  have hterm : ∀ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ≤
        (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1) * C1 := fun n hn => by
    have hb : n ∈ boxSet K F T := by
      simpa using (Finset.mem_filter.mp hn).1
    have hP := hC1 n (ne_zero_of_mem_boxSet hb)
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (absNorm_le_of_mem_boxSet hK hF hb) _) hP.2 hP.1
      (pow_nonneg (pow_nonneg hT0.le _) _)
  have hcard : (((boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n)).card : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm (bId v) : ℝ) := by
    have h1 := Formalism.HermitianLattices.Ext.L3.BoxCube.card_box_le hK hF (bId_ne_bot v) hT0.le
    have h2 : ((boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n)).card =
        Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ bId v} := by
      rw [← Set.ncard_coe_finset, ← coe_filter_box hK hF T v, ← Nat.card_coe_set_eq]
      rfl
    rw [h2]
    exact h1
  have hle := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hle
  have hexp : Formalism.HermitianLatticesTheory.fDeg K * finrank K V =
      Formalism.HermitianLatticesTheory.fDeg K + Formalism.HermitianLatticesTheory.fDeg K * (finrank K V - 1) := by
    conv_lhs => rw [show finrank K V = (finrank K V - 1) + 1 by omega]
    ring
  have hTT : T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
      (T ^ Formalism.HermitianLatticesTheory.fDeg K * (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1)) = 1 := by
    rw [zpow_neg, zpow_natCast, ← pow_mul, ← pow_add, ← hexp]
    exact inv_mul_cancel₀ (pow_ne_zero _ hT0.ne')
  have hC1n : 0 ≤ C1 := by
    have := hC1 1 one_ne_zero
    exact this.1.trans this.2
  rw [← absNorm_bId]
  calc T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n
      ≤ T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ((2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm (bId v) : ℝ)) *
          ((T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1) * C1)) := by
        refine mul_le_mul_of_nonneg_left (hle.trans ?_) (zpow_nonneg hT0.le _)
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (pow_nonneg (pow_nonneg hT0.le _) _) hC1n)
    _ = (2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1 / (Ideal.absNorm (bId v) : ℝ)) *
        (T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
          (T ^ Formalism.HermitianLatticesTheory.fDeg K * (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1))) := by ring
    _ = 2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1 / (Ideal.absNorm (bId v) : ℝ) := by rw [hTT, mul_one]
end Formalism.HermitianLattices.Ext.L3.A5
