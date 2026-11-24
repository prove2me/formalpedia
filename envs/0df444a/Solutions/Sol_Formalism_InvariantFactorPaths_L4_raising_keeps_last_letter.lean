-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.raising_keeps_last_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:10:26.454797+00:00
-- url     : https://prove2.me/submissions/3e7bf4ae-c447-4c5a-9b7a-20be00234030

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_supp_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_top
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_comm_holds
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_cartan
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
import Theorems.Thm_Formalism_CountingSumsFrames_eig_supp
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_comm
import Theorems.Thm_Formalism_CountingSumsFrames_vdm
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : UKeepsLast := by
  intro p _ K r _ LL c a hv
  set Yc : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ) with hYc
  have hYs : ∀ F ∈ Yc, F ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c} := by
    intro F hF
    rw [← supp_coe]
    exact ycond_le_supp LL (K + 1) _ hF
  have hsupp : ∀ (a : Fin r), ∀ F ∈ Yc, Uop p LL c univ a F ∈
      restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c} := by
    intro a F hF
    by_cases ha : a = 0
    · subst ha
      set G := compP (fun m => wt LL (K + 1) 0 m = c) F with hG
      have hGY : G ∈ Yc := vdm (glAct p LL (K + 1) 0 0) (wt LL (K + 1) 0) (fun x m => coeff_cartan LL (K + 1) 0 x m) Yc
        (ycond_glStable LL (K + 1) _ 0 0) F hF c
      have h0 : glAct p LL (K + 1) 0 0 G = ((c : ℤ) : ℚ_[p]) • G := by
        ext m
        rw [coeff_cartan, coeff_smul, smul_eq_mul, hG, coeff_compP]
        split_ifs with h
        · rw [h]
        · simp
      have hb : ∀ b : Fin r, b ≠ 0 → glAct p LL (K + 1) 0 b G = 0 := by
        intro b hb
        by_contra hne
        obtain ⟨m, hm⟩ := (MvPolynomial.ne_zero_iff.mp hne)
        have hm' : m ∈ (glAct p LL (K + 1) 0 b G).support := mem_support_iff.mpr hm
        have h1 := hYs _ (ycond_glStable LL (K + 1) _ 0 b G hGY)
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm')
        have h3 : glAct p LL (K + 1) 0 0 (glAct p LL (K + 1) 0 b G) =
            (((c + 1 : ℤ)) : ℚ_[p]) • glAct p LL (K + 1) 0 b G := by
          have := glAct_comm LL (K + 1) 0 0 0 b G
          rw [if_pos rfl, if_neg hb, sub_zero, h0, map_smul] at this
          rw [sub_eq_iff_eq_add.mp this]
          push_cast
          rw [add_smul, one_smul]
          abel
        have h4 := eig_supp LL (K + 1) 0 (c + 1) _ h3
        rw [mem_restrictSupport_iff] at h4
        have h5 := h4 (Finset.mem_coe.mpr hm')
        simp only [Set.mem_ofPred_eq] at h2 h5
        omega
      have hR : F - G ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c - 1} := by
        have hF' := hYs F hF
        rw [mem_restrictSupport_iff] at hF' ⊢
        intro m hm
        rw [Finset.mem_coe, mem_support_iff, coeff_sub, hG, coeff_compP] at hm
        split_ifs at hm with h
        · exact absurd (sub_self _) hm
        · rw [sub_zero] at hm
          have := hF' (Finset.mem_coe.mpr (mem_support_iff.mpr hm))
          simp only [Set.mem_ofPred_eq] at this ⊢
          omega
      have e : Uop p LL c univ 0 F = Uop p LL c univ 0 (F - G) := by
        rw [map_sub, Uop_top LL hv c G h0 hb, sub_zero]
      rw [e]
      have := Uop_supp LL hv c (c - 1) univ 0 (F - G) hR
      rw [if_pos rfl, sub_add_cancel] at this
      exact this
    · have := Uop_supp LL hv c c univ a F (hYs F hF)
      rw [if_neg ha, add_zero] at this
      exact this
  set B : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    ⨆ a : Fin r, Yc.map (Uop p LL c univ a) with hB
  have hmem : ∀ (a : Fin r), ∀ x ∈ Yc, Uop p LL c univ a x ∈ B := fun a x hx =>
    Submodule.mem_iSup_of_mem a (Submodule.mem_map_of_mem hx)
  have hle : B ≤ Yc := by
    refine le_ycond LL (K + 1) _ _ ?_ ?_
    · rw [supp_coe]
      exact iSup_le fun a => Submodule.map_le_iff_le_comap.mpr fun x hx => hsupp a x hx
    · intro s t
      have : B ≤ B.comap (glAct p LL (K + 1) s t) := by
        refine iSup_le fun a => ?_
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
        show glAct p LL (K + 1) s t (Uop p LL c univ a x) ∈ B
        have e := raising_comm_holds p K r LL c univ a s t x hv (Finset.mem_univ _) (Finset.mem_univ _)
        rw [sub_eq_iff_eq_add.mp e]
        refine Submodule.add_mem _ ?_ (hmem a _ (ycond_glStable LL (K + 1) _ s t x hx))
        split_ifs
        · exact hmem s x hx
        · exact Submodule.zero_mem _
      exact fun y hy => this hy
  intro F hF
  exact hle (hmem a F hF)
end Formalism.InvariantFactorPaths.L4
