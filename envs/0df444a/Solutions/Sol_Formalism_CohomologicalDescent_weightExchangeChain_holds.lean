-- Prove2me | solution 1 for Formalism.CohomologicalDescent.weightExchangeChain_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:06.728798+00:00
-- url     : https://prove2.me/submissions/7cc2895a-467c-4f1b-8d18-99c6ad55b3c6

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_WEChain
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ContentLinkageHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
import Theorems.Thm_Formalism_CohomologicalDescent_map_cast_image_val_eq
import Theorems.Thm_Formalism_CohomologicalDescent_sum_filter_block_eq
import Theorems.Thm_Formalism_CohomologicalDescent_contentLinkage_holds
import Theorems.Thm_Formalism_CohomologicalDescent_shiftSumBound_holds
import Theorems.Thm_Formalism_CohomologicalDescent_weightExchangeBound_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution : WEChain := by
  intro k j t q l h κ K _ _ U U' V V' b b' c c' kc kp hl htl hU hU' hV hV' hU0 hU'h hsum hblock hVb
    hprodU hprodV hkc hkp hmU hmV hfilt
  have hlink := contentLinkage_holds l K _ U U' c hl hprodU
  have hlinkV := contentLinkage_holds l K _ V V' c' hl hprodV
  have hmemU : ∀ s : Fin t, b + ((s : ℕ) : ℤ) ∈ Finset.univ.image U := by
    intro s
    have hs := s.isLt
    refine Finset.mem_image.mpr ⟨⟨k + j + t - 1 - (s : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
    have h1 : k + j + t - 1 - (k + j + t - 1 - (s : ℕ)) = (s : ℕ) := by omega
    rw [hblock _ (by simp only; omega) (by simp only; omega)]
    simp only [h1]
  have hmemV : ∀ s : Fin t, b' + ((s : ℕ) : ℤ) ∈ Finset.univ.image V := by
    intro s
    obtain ⟨a, ha⟩ := hVb s
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
  have hKU : |∑ s, kc s| ≤ (mwCount l b t κ (Finset.univ.image U) : ℤ) * ((t : ℤ) + 2 * κ) := by
    refine shiftSumBound_holds l b t κ (Finset.univ.image U) kc hl.pos htl hmemU hkc ?_
    rw [map_cast_image_val_eq l _ U hU, hlink]
    exact hmU
  have hKV : |∑ s, kp s| ≤ (mwCount l b' t κ (Finset.univ.image V) : ℤ) * ((t : ℤ) + 2 * κ) := by
    refine shiftSumBound_holds l b' t κ (Finset.univ.image V) kp hl.pos htl hmemV hkp ?_
    rw [map_cast_image_val_eq l _ V hV, hlinkV]
    exact hmV
  have hfilt' : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a) +
        (l : ℤ) * (∑ s, kp s) - ∑ s, kc s := by
    rw [sum_filter_block_eq k j t q U b hblock]
    refine hfilt.trans (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact weightExchangeBound_holds k j t q l h κ _ _ U U' (∑ s, kc s) (∑ s, kp s) hU hU' hU0 hU'h hsum hfilt'
    hKU hKV
end Formalism.CohomologicalDescent
