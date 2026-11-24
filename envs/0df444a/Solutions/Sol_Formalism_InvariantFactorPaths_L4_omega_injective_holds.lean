-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.omega_injective_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:36:52.369817+00:00
-- url     : https://prove2.me/submissions/5955a15b-7482-40df-b708-06795611caf7

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_exists_top
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_strip_le
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_omega_top
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_enum_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_omega_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typesLE_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_exists_hwC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_first_weight_le_of_support
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_setLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_hWC_setLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typesLE_le_ycondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_le_supp
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
theorem _root_.solution : OmegaInj := by
  intro p _ K r _ LL ρ c o hr hρ hv x hx hΩ
  by_contra hx0
  have h0ρ : (0 : Fin r) ∈ univ.erase ρ := by
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have := congrArg Fin.val he
    rw [Fin.val_zero] at this
    omega
  set S : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    (Pol p r (setLast LL (o + 1)) ⊓ FreeOf p (Fin.last K, ρ) ⊓
      TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)) ⊓ LinearMap.ker (Omega p LL c ρ) with hS
  have hmem : ∀ z, z ∈ S ↔ ((z ∈ Pol p r (setLast LL (o + 1)) ∧ z ∈ FreeOf p (Fin.last K, ρ)) ∧
      z ∈ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)) ∧ Omega p LL c ρ z = 0 := by
    intro z
    simp only [hS, Submodule.mem_inf, LinearMap.mem_ker]
  have hstab : ∀ s ∈ univ.erase ρ, ∀ t ∈ univ.erase ρ, ∀ z ∈ S, glAct p (setLast LL (o + 1)) (K + 1) s t z ∈ S := by
    intro s hs t ht z hz
    rw [hmem] at hz ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hz
    refine ⟨⟨⟨glAct_pol (setLast LL (o + 1)) (K + 1) s t z h1, ?_⟩, ?_⟩, ?_⟩
    · exact glAct_free LL (K + 1) s t _ (Finset.ne_of_mem_erase hs) (Finset.ne_of_mem_erase ht) z h2
    · exact typesLE_glStable LL (K + 1) _ _ s t hs ht z h3
    · rw [glAct_setLast, ← omega_comm LL hv ρ c s t hs ht z, h4, map_zero]
  obtain ⟨h, hhS, hh0, th, hhw⟩ := exists_hwC (setLast LL (o + 1)) (K + 1) (univ.erase ρ) S
    (fun z hz => ((hmem z).mp hz).1.1.1) hstab x (Submodule.mem_inf.mpr ⟨hx, LinearMap.mem_ker.mpr hΩ⟩) hx0
  rw [hWC_setLast] at hhw
  obtain ⟨⟨⟨hP, hF⟩, hT⟩, hO⟩ := (hmem h).mp hhS
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
  have hsum : ∑ a, β a = o + 1 := by
    rw [Pol, mem_restrictSupport_iff] at hP
    have h1 := hP (Finset.mem_coe.mpr hm) (Fin.last K)
    have h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1 := by simp [setLast]
    rw [h2] at h1
    rw [← hmβ]
    simp only [wp]
    exact_mod_cast h1
  have hE := enum_pos ρ hr hρ c o th β hβ hβρ hsum hth0
    (fun a ha a' ha' haa => strip_le LL hv _ th h hhw β hy htop hβ a a' ha ha' haa)
  have h1 := omega_top LL hv ρ c o th h hP hF hhw β htop
  rw [hO, map_zero] at h1
  rcases smul_eq_zero.mp h1.symm with h2 | h2
  · have := Int.cast_eq_zero.mp h2
    omega
  · exact hy h2
end Formalism.InvariantFactorPaths.L4
