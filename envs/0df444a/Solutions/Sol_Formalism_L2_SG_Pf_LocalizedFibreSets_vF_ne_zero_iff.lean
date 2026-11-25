-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalizedFibreSets.vF_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:43.553383+00:00
-- url     : https://prove2.me/submissions/a0e257cd-a098-4f09-a52a-31bf868b9e28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_PhiCountingHolds
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)]
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {x : 𝓞 F} (hx : x ≠ 0) :
    vF 𝔭 x ≠ 0 ↔ x ∈ 𝔭 := by
  constructor
  · intro h
    by_contra hx'
    apply h
    apply Nat.eq_zero_of_le_zero
    show sSup {e : ℕ | x ∈ 𝔭 ^ e} ≤ 0
    apply csSup_le'
    intro e he
    by_contra hne
    exact hx' (Ideal.pow_le_self (by omega) he)
  · intro hx'
    have hbdd : BddAbove {e : ℕ | x ∈ 𝔭 ^ e} := by
      have h0 : x ∉ ⨅ n : ℕ, 𝔭 ^ n := by
        rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top]
        simpa using hx
      simp only [Submodule.mem_iInf, not_forall] at h0
      obtain ⟨n, hn⟩ := h0
      refine ⟨n, fun e he => ?_⟩
      by_contra hlt
      push_neg at hlt
      exact hn (Ideal.pow_le_pow_right hlt.le he)
    have h1 : 1 ≤ sSup {e : ℕ | x ∈ 𝔭 ^ e} :=
      le_csSup hbdd (show x ∈ 𝔭 ^ 1 by rwa [pow_one])
    show sSup {e : ℕ | x ∈ 𝔭 ^ e} ≠ 0
    omega
end Formalism.L2.SG.Pf.LocalizedFibreSets
