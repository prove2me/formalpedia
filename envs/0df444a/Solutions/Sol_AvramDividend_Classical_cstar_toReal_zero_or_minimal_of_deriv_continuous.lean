-- Prove2me | solution 1 for AvramDividend.Classical.cstar_toReal_zero_or_minimal_of_deriv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T16:48:57.195264+00:00
-- url     : https://prove2.me/submissions/1195e07f-7a55-40a1-96f6-d7697a51594e

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_continuous_argmin_sInf_zero_or_minimal

open Set
open scoped ENNReal
open AvramDividend.Classical

private theorem toReal_iInf_ofReal_of_positive (s : Set ℝ)
    (hne : s.Nonempty) (hpos : ∀ a ∈ s, 0 < a) :
    (⨅ a ∈ s, ENNReal.ofReal a).toReal = sInf s := by
  classical
  have hs : (⨅ a ∈ s, ENNReal.ofReal a) =
      sInf (ENNReal.ofReal '' s) := by
    exact (csInf_image (s := s) (f := ENNReal.ofReal)
      (hf := OrderBot.bddBelow _)
      (hf' := by
        simpa only [sInf_empty] using
          (le_top : (⨅ i : s, ENNReal.ofReal (i : ℝ)) ≤ (⊤ : ℝ≥0∞)))).symm
  rw [hs, ENNReal.toReal_sInf]
  · have himage : ENNReal.toReal '' (ENNReal.ofReal '' s) = s := by
      ext a
      constructor
      · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
        simpa only [ENNReal.toReal_ofReal (hpos c hc).le] using hc
      · intro ha
        exact ⟨ENNReal.ofReal a, ⟨a, ha, rfl⟩,
          ENNReal.toReal_ofReal (hpos a ha).le⟩
    rw [himage]
  · rintro a ⟨b, hb, rfl⟩
    exact ENNReal.ofReal_ne_top

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Ioi 0)) :
    (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x →
          deriv W (cstar W).toReal ≤ deriv W x) := by
  classical
  by_cases hne : (cstarSet W).Nonempty
  · have hs : (cstar W).toReal = sInf (cstarSet W) := by
      rw [cstar, if_pos hne]
      exact toReal_iInf_ofReal_of_positive _ hne (by
        intro a ha
        exact ha.1)
    rw [hs]
    exact continuous_argmin_sInf_zero_or_minimal (deriv W) hcont hne
  · left
    rw [cstar, if_neg hne]
    by_cases hz : ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal)
    · rw [if_pos hz]
      rfl
    · rw [if_neg hz]
      rfl
