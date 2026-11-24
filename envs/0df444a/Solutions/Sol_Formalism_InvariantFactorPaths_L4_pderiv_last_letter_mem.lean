-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pderiv_last_letter_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:04.170172+00:00
-- url     : https://prove2.me/submissions/6b517ef3-8830-42b7-b7d3-650c77c92b00

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_xsp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_zero_mem_erase
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_pol
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_freeOf
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_ycond_early
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_pderiv
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_typesLE_of_ycondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typesLE_le_ycondC


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
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ a : Fin r)
    (o : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LL.vec (Fin.last K) = true)
    (hTP : ∀ Mt : WithTop ℤ, ∃ P, IsTypeProj p LL (K + 1) (univ.erase ρ) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P)
    (ha : a ≠ ρ) :
    ∀ x ∈ XSp p (setLast LL (o + 1)) J M ρ, pderiv (Fin.last K, a) x ∈ XSp p (setLast LL o) J M ρ := by
  intro x hx
  rw [mem_xsp] at hx ⊢
  obtain ⟨hxP, hxF, hxk⟩ := hx
  have hdP := pderiv_pol LL a o x hxP
  have h0 := zero_mem_erase ρ hr hρ
  refine ⟨hdP, pderiv_freeOf _ _ x hxF, fun k => ⟨fun hk => ⟨?_, ?_⟩, fun hk => ?_⟩⟩
  · exact pderiv_ycond_early LL K le_rfl (M k) a x ((hxk k).1 hk).1
  · obtain ⟨P, hP⟩ := hTP (M k)
    refine mem_typesLE_of_ycondC (setLast LL o) (K + 1) _ h0 (M k) P hP _ (Submodule.mem_inf.mpr ⟨?_, hdP⟩)
    exact ycondC_pderiv LL hv _ (M k) a (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩) x
      (typesLE_le_ycondC LL (K + 1) _ h0 (M k) ((hxk k).1 hk).2)
  · exact pderiv_ycond_early LL (J k) (by omega) (M k) a x ((hxk k).2 hk)
end Formalism.InvariantFactorPaths.L4
