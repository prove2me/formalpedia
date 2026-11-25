-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G3.spanS_le_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:34:03.05333+00:00
-- url     : https://prove2.me/submissions/3c02860a-2f9d-484c-b790-a79687961b4c

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanSSelf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HermitianCoefficientIdentityOne
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


section
open Module
noncomputable section
namespace Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
private theorem mem_iff_lemma {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl
private theorem smul_mem_lemma_2 {ι : Type} [Fintype ι] {g : ι → V} {a : K} (ha : a ∈ S) {v : V}
    (hv : v ∈ spanS S g) : a • v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv ⊢
  obtain ⟨d, hd, rfl⟩ := hv
  exact ⟨fun i => a * d i, fun i => S.mul_mem ha (hd i), by simp [Finset.smul_sum, mul_smul]⟩
end
end Formalism.L2.SG.Pf.G3
end
end

set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V} {g : ι → V}
    (hfg : ∀ k, f k ∈ spanS S g) {v : V} (hv : v ∈ spanS S f) : v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, hc, rfl⟩ := hv
  exact AddSubgroup.sum_mem _ fun k _ => smul_mem_lemma_2 (hc k) (hfg k)
end Formalism.L2.SG.Pf.G3
