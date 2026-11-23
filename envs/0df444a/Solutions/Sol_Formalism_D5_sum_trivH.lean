-- Prove2me | solution 1 for Formalism.D5.sum_trivH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:18.096255+00:00
-- url     : https://prove2.me/submissions/037d4926-e40c-490b-a958-ffbf61ce57f7

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_trivH_cases
import Theorems.Thm_Formalism_D5_cyclicCharacter_first_basis
import Theorems.Thm_Formalism_D5_quadraticCharacter_first_basis
import Theorems.Thm_Formalism_D5_productCharacter_first_basis
import Theorems.Thm_Formalism_D5_cyclicCharacter_second_basis
import Theorems.Thm_Formalism_D5_quadraticCharacter_second_basis
import Theorems.Thm_Formalism_D5_productCharacter_second_basis
import Theorems.Thm_Formalism_D5_trivH_zero
import Theorems.Thm_Formalism_D5_trivH_chC
import Theorems.Thm_Formalism_D5_trivH_psC
import Theorems.Thm_Formalism_D5_trivH_chpsC
import Theorems.Thm_Formalism_D5_ne_of_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
open Classical
namespace Formalism.D5
theorem _root_.solution (Hs : CycHost H) (F : AddChar (E0 × H) ℂ → ℂ) :
    ∑ ψ : AddChar (E0 × H) ℂ, (if TrivH ψ then ψ e10 * F ψ else 0)
      = F 0 + F Hs.psC - F Hs.chC - F Hs.chpsC := by
  have hmem : ∀ ψ : AddChar (E0 × H) ℂ,
      TrivH ψ ↔ ψ ∈ ({0, Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)) := by
    intro ψ
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact trivH_cases Hs ψ
    · rintro (rfl | rfl | rfl | rfl)
      exacts [trivH_zero, trivH_chC Hs, trivH_psC Hs, trivH_chpsC Hs]
  have h1 : ∑ ψ ∈ ({0, Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)),
      (if TrivH ψ then ψ e10 * F ψ else 0)
      = ∑ ψ : AddChar (E0 × H) ℂ, (if TrivH ψ then ψ e10 * F ψ else 0) :=
    Finset.sum_subset (Finset.subset_univ _) (fun ψ _ hψ => if_neg (fun h => hψ ((hmem ψ).1 h)))
  rw [← h1]
  have n1 : (0 : AddChar (E0 × H) ℂ) ∉
      ({Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne_of_val e10 ?_, ne_of_val e01 ?_, ne_of_val e10 ?_⟩
    · rw [AddChar.zero_apply, cyclicCharacter_first_basis]; norm_num
    · rw [AddChar.zero_apply, quadraticCharacter_second_basis]; norm_num
    · rw [AddChar.zero_apply, productCharacter_first_basis]; norm_num
  have n2 : Hs.chC ∉ ({Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne_of_val e10 ?_, ne_of_val e01 ?_⟩
    · rw [cyclicCharacter_first_basis, quadraticCharacter_first_basis]; norm_num
    · rw [cyclicCharacter_second_basis, productCharacter_second_basis]; norm_num
  have n3 : Hs.psC ∉ ({Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)) := by
    simp only [Finset.mem_singleton]
    exact ne_of_val e10 (by rw [quadraticCharacter_first_basis, productCharacter_first_basis]; norm_num)
  rw [Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, Finset.sum_singleton,
    if_pos (trivH_zero (H := H)), if_pos (trivH_chC Hs), if_pos (trivH_psC Hs),
    if_pos (trivH_chpsC Hs), AddChar.zero_apply, cyclicCharacter_first_basis, quadraticCharacter_first_basis, productCharacter_first_basis]
  ring
end Formalism.D5
