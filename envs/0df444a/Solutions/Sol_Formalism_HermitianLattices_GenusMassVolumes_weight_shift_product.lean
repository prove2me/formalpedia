-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.weight_shift_product
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:53.663743+00:00
-- url     : https://prove2.me/submissions/b920cfa8-a753-4bb1-bc1a-d4940e9abe57

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightShiftProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : OppositeSignRhoDifferenceEqCard := by
  intro N sg rhoN a b hab hs
  have h1 : (univ.filter (fun c => a < c ∧ sg c ≠ sg a)).card =
      (univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card +
        (univ.filter (fun c => b < c ∧ sg c ≠ sg b)).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h, h'⟩
        rcases lt_trichotomy c b with hc | hc | hc
        · exact Or.inl ⟨h, hc, h'⟩
        · exact absurd (hc ▸ hs.symm) h'
        · exact Or.inr ⟨hc, hs ▸ h'⟩
      · rintro (⟨h, _, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, h'⟩
        · exact ⟨hab.trans h, hs ▸ h'⟩
    · rw [disjoint_left]
      intro c hc hc'
      simp only [mem_filter, mem_univ, true_and] at hc hc'
      exact absurd hc.2.1 (not_lt.mpr hc'.1.le)
  have h2 : (univ.filter (fun c => c < b ∧ sg c ≠ sg b)).card =
      (univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card +
        (univ.filter (fun c => c < a ∧ sg c ≠ sg a)).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h, h'⟩
        rcases lt_trichotomy c a with hc | hc | hc
        · exact Or.inr ⟨hc, hs ▸ h'⟩
        · exact absurd (hc ▸ hs) h'
        · exact Or.inl ⟨hc, h, hs ▸ h'⟩
      · rintro (⟨_, h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, hs ▸ h'⟩
        · exact ⟨h.trans hab, hs ▸ h'⟩
    · rw [disjoint_left]
      intro c hc hc'
      simp only [mem_filter, mem_univ, true_and] at hc hc'
      exact absurd hc.1 (not_lt.mpr hc'.1.le)
  simp only [rhoN]
  rw [h1, h2]
  push_cast
  ring
end Formalism.HermitianLattices.GenusMassVolumes
