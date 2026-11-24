-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restriction_into_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:01.530965+00:00
-- url     : https://prove2.me/submissions/220e4a1b-fd07-4ba2-974b-5821f4a9b575

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_keep_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_ne_of_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_condition_drop_holds
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_keep
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_min
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_typesLE_of_ycondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_keep
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_le_ycondC
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
theorem _root_.solution : ResInto := by
  intro p _ K r _ LL q J M ρ e1 hr hρ hv hHP h hh
  obtain ⟨hhP, hhY⟩ := Submodule.mem_inf.mp hh
  rw [Submodule.mem_iInf] at hhY
  change resL p (Fin.last K, ρ) 0 h ∈ XSp p LL J M ρ
  have hresP : resL p (Fin.last K, ρ) 0 h ∈ Pol p r LL := resL_keep_supp (Fin.last K, ρ) 0 _ h hhP
  have key : ∀ j ≤ K, ∀ Mt : WithTop ℤ, ∀ x ∈ YCond p LL j Mt, resL p (Fin.last K, ρ) 0 x ∈ YCond p LL j Mt :=
    fun j hj Mt => ycond_keep LL j Mt (resL p (Fin.last K, ρ) 0)
      (fun c d x => resL_glAct LL j c d (Fin.last K, ρ) 0 (fun i hi =>
        ⟨fun h' => last_ne_of_lt i (by omega) (Prod.mk.inj h').1.symm,
          fun h' => last_ne_of_lt i (by omega) (Prod.mk.inj h').1.symm⟩) x)
      (resL_keep_supp (Fin.last K, ρ) 0 _)
  unfold XSp
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hresP, resL_free (Fin.last K, ρ) h⟩, ?_⟩
  rw [Submodule.mem_iInf]
  intro k
  split_ifs with hk
  · have h1 : h ∈ YCond p LL (K + 1) (M k) := by
      have := hhY k
      rw [ycond_min, min_eq_right hk] at this
      exact this
    refine Submodule.mem_inf.mpr ⟨key K le_rfl _ _ (condition_drop_holds p K r LL (M k) hv h hhP h1), ?_⟩
    have h0 : (0 : Fin r) ∈ (univ : Finset (Fin r)).erase ρ := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h'
      have := congrArg Fin.val h'
      simp at this
      omega
    obtain ⟨P, hP, -, -⟩ := hHP.1 (K + 1) le_rfl (univ.erase ρ) (Or.inr rfl)
      {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} (fun la la' hl => by
        show (((la 0 : ℤ) : WithTop ℤ) ≤ M k) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ M k)
        rw [hl 0 h0])
    refine mem_typesLE_of_ycondC LL (K + 1) _ h0 (M k) P hP _ (Submodule.mem_inf.mpr ⟨?_, hresP⟩)
    refine ycondC_keep LL (K + 1) _ (M k) (resL p (Fin.last K, ρ) 0) (fun c hc d hd x =>
      resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 (fun i _ =>
        ⟨fun h' => (Finset.mem_erase.mp hc).1 (Prod.mk.inj h').2,
          fun h' => (Finset.mem_erase.mp hd).1 (Prod.mk.inj h').2⟩) x)
      (resL_keep_supp (Fin.last K, ρ) 0 _) h (ycond_le_ycondC LL (K + 1) _ (M k) h1)
  · exact key (J k) (by omega) _ _ (hhY k)
end Formalism.InvariantFactorPaths.L4
