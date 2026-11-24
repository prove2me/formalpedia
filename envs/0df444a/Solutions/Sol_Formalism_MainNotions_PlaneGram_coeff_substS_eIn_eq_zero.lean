-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_substS_eIn_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:45.168803+00:00
-- url     : https://prove2.me/submissions/25a1d5c1-5453-4219-a4ad-01fbe8ce05dc

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_mem
import Theorems.Thm_Formalism_MainNotions_PlaneGram_subX_mem_supported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
variable (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α δ : L × Fin r →₀ ℕ) (hδ : eOut out δ ≠ 0) :
    (substS ι sg S A B (monomial (eIn out α) 1)).coeff δ = 0 := by
  have hmem : substS ι sg S A B (monomial (eIn out α) 1) ∈
      (supported R {y : L × Fin r | ¬ out y.1}).toSubring := by
    refine substS_mem ι sg S A B _ (fun c => Subalgebra.algebraMap_mem _ _) _ ?_
    intro γ hγ x hx
    refine subX_mem_supported sg S A B out x ?_
    have hγ' : γ = eIn out α := by
      classical
      have := support_monomial_subset hγ
      simpa using this
    rw [hγ', Finsupp.mem_support_iff, eIn_apply] at hx
    intro ho
    rw [if_pos ho] at hx
    exact hx rfl
  have hv := mem_supported.mp (Subalgebra.mem_toSubring.mp hmem)
  by_contra hne
  apply hδ
  ext x
  rw [eOut_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with ho
  · by_contra hx
    have : x ∈ (substS ι sg S A B (monomial (eIn out α) 1)).vars :=
      (mem_vars_iff_mem_support x).mpr ⟨δ, mem_support_iff.mpr hne, Finsupp.mem_support_iff.mpr hx⟩
    exact hv (Finset.mem_coe.mpr this) ho
  · rfl
end Formalism.MainNotions.PlaneGram
