-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restriction_mem_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:56.875961+00:00
-- url     : https://prove2.me/submissions/14e69d39-c146-4bb0-9861-1850bb1435fc

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_xsp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_zero_mem_erase
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_keep
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_min
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_condition_drop_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_ne_of_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_typesLE_of_ycondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_keep_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_keep
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_le_ycondC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hTP : ∀ Mt : WithTop ℤ, ∃ P, IsTypeProj p LL (K + 1) (univ.erase ρ) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P) :
    ∀ h ∈ Y p LL J M, resL p (Fin.last K, ρ) 0 h ∈ XSp p LL J M ρ := by
  intro h hh
  rw [mem_y] at hh
  obtain ⟨hhP, hhY⟩ := hh
  have hresP : resL p (Fin.last K, ρ) 0 h ∈ Pol p r LL := resL_keep_supp (Fin.last K, ρ) 0 _ h hhP
  have key : ∀ j ≤ K, ∀ Mt : WithTop ℤ, ∀ x ∈ YCond p LL j Mt, resL p (Fin.last K, ρ) 0 x ∈ YCond p LL j Mt :=
    fun j hj Mt => ycond_keep LL j Mt (resL p (Fin.last K, ρ) 0)
      (fun c d x => resL_glAct LL j c d (Fin.last K, ρ) 0 (fun i hi =>
        ⟨fun h' => last_ne_of_lt i (by omega) (Prod.mk.inj h').1.symm,
          fun h' => last_ne_of_lt i (by omega) (Prod.mk.inj h').1.symm⟩) x)
      (resL_keep_supp (Fin.last K, ρ) 0 _)
  have h0 := zero_mem_erase ρ hr hρ
  rw [mem_xsp]
  refine ⟨hresP, resL_free (Fin.last K, ρ) h, fun k => ⟨fun hk => ?_, fun hk => key (J k) (by omega) _ _ (hhY k)⟩⟩
  have h1 : h ∈ YCond p LL (K + 1) (M k) := by
    have := hhY k
    rw [ycond_min, min_eq_right hk] at this
    exact this
  refine ⟨key K le_rfl _ _ (condition_drop_holds p K r LL (M k) hv h hhP h1), ?_⟩
  obtain ⟨P, hP⟩ := hTP (M k)
  refine mem_typesLE_of_ycondC LL (K + 1) _ h0 (M k) P hP _ (Submodule.mem_inf.mpr ⟨?_, hresP⟩)
  refine ycondC_keep LL (K + 1) _ (M k) (resL p (Fin.last K, ρ) 0) (fun c hc d hd x =>
    resL_glAct LL (K + 1) c d (Fin.last K, ρ) 0 (fun i _ =>
      ⟨fun h' => (Finset.mem_erase.mp hc).1 (Prod.mk.inj h').2,
        fun h' => (Finset.mem_erase.mp hd).1 (Prod.mk.inj h').2⟩) x)
    (resL_keep_supp (Fin.last K, ρ) 0 _) h (ycond_le_ycondC LL (K + 1) _ (M k) h1)
end Formalism.InvariantFactorPaths.L4
