-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G3.sd_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:30.515798+00:00
-- url     : https://prove2.me/submissions/07274104-0189-4462-97a9-f69c5855057b

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanSSelf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SdBasisBot
import Theorems.Thm_Formalism_L2_SG_Pf_G3_sd_basis_bot
import Theorems.Thm_Formalism_L2_SG_Pf_G3_sup_cutW
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_unit_norm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_finrank_cutW_lt
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutM
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_proj_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_symm_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_int
import Theorems.Thm_Formalism_L2_SG_Pf_G3_mem_spanS_self
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
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) : ∀ (n : ℕ) (W : Submodule K V) (M : AddSubgroup V),
    finrank K W ≤ n → IsSD S h W M →
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  intro n
  induction n with
  | zero =>
    intro W M hn hM
    exact sd_basis_bot hM (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn))
  | succ n ih =>
    intro W M hn hM
    by_cases hbot : W = ⊥
    · exact sd_basis_bot hM hbot
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    have hxW := hM.le x hx
    obtain ⟨k, f, hfo, hfu, hfM, hfW⟩ := ih _ _
      (by have := finrank_cutW_lt (h := h) hxW hu.1; omega) (hM.cut hx hu)
    have hfc : ∀ i, f i ∈ cutW h W x := fun i => by
      rw [← hfW]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hfm : ∀ i, f i ∈ M := fun i =>
      (mem_cutM.mp ((hfM (f i)).mp (mem_spanS_self f i))).1
    refine ⟨k + 1, Fin.cons x f, ?_, ?_, fun v => ?_, ?_⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_cutW.mp (hfc j)).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa using symm_zero hs (mem_cutW.mp (hfc i)).2
        | succ j =>
          simpa using hfo i j (fun h' => hij (by rw [h']))
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hfu i
    · constructor
      · rintro ⟨c, hc, rfl⟩
        refine M.sum_mem fun i _ => hM.smul_mem _ (hc i) _ ?_
        cases i using Fin.cases with
        | zero => simpa using hx
        | succ i => simpa using hfm i
      · intro hv
        obtain ⟨d, hd', hdv⟩ := (hfM _).mpr (proj_mem hM.toIsLatIn hx hu hv)
        refine ⟨Fin.cons (h x v * (h x x)⁻¹) d, fun i => ?_, ?_⟩
        · cases i using Fin.cases with
          | zero => simpa using S.mul_mem (hM.int _ hx _ hv) hu.2.2
          | succ i => simpa using hd' i
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hdv]
          abel
    · rw [Fin.range_cons, Submodule.span_insert, hfW]
      exact sup_cutW hxW hu.1
end Formalism.L2.SG.Pf.G3
