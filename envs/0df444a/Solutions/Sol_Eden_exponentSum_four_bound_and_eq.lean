-- Prove2me | solution 1 for Eden.exponentSum_four_bound_and_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:42.796417+00:00
-- url     : https://prove2.me/submissions/52990afa-59ae-4194-8bdf-e015ca602788

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_one
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap
import Theorems.Thm_Eden_descending_radiusPairSpectrum_two_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_one
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero
import Theorems.Thm_Eden_limitingSquaredRadius_cases
import Theorems.Thm_Eden_limitingSquaredRadius_eq_one_iff
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    spectrumPartialSum (lyapunovExponent c p) 4 ≤ 4 ∧
      (spectrumPartialSum (lyapunovExponent c p) 4 = 4 ↔
        radiusSq₁ p = 1 ∧ radiusSq₂ p = 1) := by
  rw [← limitingSquaredRadius_eq_one_iff (radiusSq₁ p),
    ← limitingSquaredRadius_eq_one_iff (radiusSq₂ p),
    lyapunovExponent_eq_radiusPairSpectrum]
  rcases limitingSquaredRadius_cases (radiusSq₁ p) with h₁ | h₁ | h₁ <;>
    rcases limitingSquaredRadius_cases (radiusSq₂ p) with h₂ | h₂ | h₂
  all_goals rw [h₁, h₂]
  all_goals try rw [descending_radiusPairSpectrum_swap c 1 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 0]
  all_goals try rw [descending_radiusPairSpectrum_swap c 2 1]
  all_goals norm_num [descending_radiusPairSpectrum_zero_zero hc,
    descending_radiusPairSpectrum_zero_one hc, descending_radiusPairSpectrum_zero_two hc,
    descending_radiusPairSpectrum_one_one hc, descending_radiusPairSpectrum_one_two hc,
    descending_radiusPairSpectrum_two_two hc, spectrumPartialSum, spectrumEntry,
    Finset.sum_range_succ]
end Eden
