-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.space_vanishing_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:42.4858+00:00
-- url     : https://prove2.me/submissions/0de81a33-10bd-4d64-b8eb-71f4c9c20269

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_abs_wt_early
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_strip_sum
import Theorems.Thm_Formalism_CountingSumsFrames_eig_supp
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_compL
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eJ_cw_diag
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_exists_hwC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_exists_top
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_first_weight_le_of_support
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_hWC_setLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_strip_le
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sum_erase_last
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typesLE_glStable
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typesLE_le_ycondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_le_supp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : XVanish := by
  intro p _ K r _ LL ρ c o hr hρ hv hco
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  have h0ρ : (0 : Fin r) ∈ univ.erase ρ := by
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have := congrArg Fin.val he
    rw [Fin.val_zero] at this
    omega
  set S : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    Pol p r (setLast LL o) ⊓ FreeOf p (Fin.last K, ρ) ⊓
      TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) with hS
  have hmem : ∀ z, z ∈ S ↔ (z ∈ Pol p r (setLast LL o) ∧ z ∈ FreeOf p (Fin.last K, ρ)) ∧
      z ∈ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) := by
    intro z
    simp only [hS, Submodule.mem_inf]
  have hstab : ∀ s ∈ univ.erase ρ, ∀ t ∈ univ.erase ρ, ∀ z ∈ S, glAct p (setLast LL o) (K + 1) s t z ∈ S := by
    intro s hs t ht z hz
    rw [hmem] at hz ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    refine ⟨⟨glAct_pol (setLast LL o) (K + 1) s t z h1, ?_⟩, ?_⟩
    · exact glAct_free LL (K + 1) s t _ (Finset.ne_of_mem_erase hs) (Finset.ne_of_mem_erase ht) z h2
    · exact typesLE_glStable LL (K + 1) _ _ s t hs ht z h3
  obtain ⟨h, hhS, hh0, th, hhw⟩ := exists_hwC (setLast LL o) (K + 1) (univ.erase ρ) S
    (fun z hz => ((hmem z).mp hz).1.1) hstab x hx hx0
  rw [hWC_setLast] at hhw
  obtain ⟨⟨hP, hF⟩, hT⟩ := (hmem h).mp hhS
  have hth0 : th 0 ≤ c := by
    have := first_weight_le_of_support LL (K + 1) (univ.erase ρ) h0ρ ((c : ℤ) : WithTop ℤ) th h hh0
      (ycondC_le_supp LL (K + 1) _ _ (typesLE_le_ycondC LL (K + 1) _ h0ρ _ hT)) (Submodule.mem_inf.mp hhw).1
    exact WithTop.coe_le_coe.mp this
  obtain ⟨β, hy, htop, m, hm, hmβ⟩ := exists_top h hh0
  have hβ : ∀ a, 0 ≤ β a := fun a => by rw [← hmβ]; exact Int.natCast_nonneg _
  have hβρ : β ρ = 0 := by
    rw [FreeOf, mem_restrictSupport_iff] at hF
    have := hF (Finset.mem_coe.mpr hm)
    simp only [Set.mem_ofPred_eq] at this
    rw [← hmβ]; simp only [wp, this]; rfl
  rw [Pol, mem_restrictSupport_iff] at hP
  have hmd : MultiDeg (setLast LL o) m := hP (Finset.mem_coe.mpr hm)
  have hsum : ∑ a, β a = o := by
    have h1 := hmd (Fin.last K)
    have h2 : (setLast LL o).deg (Fin.last K) = o := by simp [setLast]
    rw [h2] at h1
    rw [← hmβ]
    simp only [wp]
    exact_mod_cast h1
  have hstrip : ∀ a ∈ univ.erase ρ, ∀ a' ∈ univ.erase ρ, a < a' → th a' ≤ th a - β a :=
    fun a ha a' ha' haa => strip_le LL hv _ th h hhw β hy htop hβ a a' ha ha' haa

  have hwt : ∀ a ∈ univ.erase ρ, wt LL K a m = th a - β a := by
    intro a ha
    have h1 := eig_supp LL K a _ _ (eJ_cw_diag LL hv _ th h hhw a ha β)
    rw [mem_restrictSupport_iff] at h1
    refine h1 (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))
    rw [cw, coeff_compL, if_pos hmβ]
    exact mem_support_iff.mp hm

  let tN : ℕ → ℤ := fun i => if h : i < r then th ⟨i, h⟩ else 0
  let bN : ℕ → ℤ := fun i => if h : i < r then β ⟨i, h⟩ else 0
  have htN : ∀ a : Fin r, tN (a : ℕ) = th a := fun a => by simp only [tN, dif_pos a.isLt, Fin.eta]
  have hbN : ∀ a : Fin r, bN (a : ℕ) = β a := fun a => by simp only [bN, dif_pos a.isLt, Fin.eta]
  have hCs : ∀ i, (h : i < r - 1) → (⟨i, by omega⟩ : Fin r) ∈ univ.erase ρ := by
    intro i h
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have := congrArg Fin.val he
    simp only at this
    omega
  have hSb : ∑ a ∈ range (r - 1), bN a = o := by
    rw [← sum_erase_last ρ hρ bN, ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), hβρ, zero_add]
    exact Finset.sum_congr rfl fun a _ => hbN a
  have key := strip_sum tN bN (r - 1) (by
    intro i hi
    have h1 := hstrip ⟨i, by omega⟩ (hCs i (by omega)) ⟨i + 1, by omega⟩ (hCs (i + 1) hi)
      (by simp only [Fin.lt_def]; omega)
    have h2 := htN ⟨i, by omega⟩
    have h3 := htN ⟨i + 1, by omega⟩
    have h4 := hbN ⟨i, by omega⟩
    simp only at h2 h3 h4
    rw [h2, h3, h4]
    exact h1) (r - 2) (by omega)
  have e1 : r - 2 + 1 = r - 1 := by omega
  rw [e1, hSb] at key
  have h5 := htN ⟨r - 2, by omega⟩
  have h6 := hbN ⟨r - 2, by omega⟩
  have h7 := htN 0
  rw [Fin.val_zero] at h7
  simp only at h5 h6
  rw [h5, h6, h7, ← hwt _ (hCs (r - 2) (by omega))] at key
  have h8 := (abs_le.mp (abs_wt_early LL o (⟨r - 2, by omega⟩ : Fin r) m hmd)).1
  linarith
end Formalism.InvariantFactorPaths.L4
