-- Prove2me | solution 1 for Eden.periodicGlobalGrowthInterpolation_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:27:06.000628+00:00
-- url     : https://prove2.me/submissions/2e1ff3dc-ebb2-4fe6-a6ca-7197bd00bad9

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
import Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_eq
import Theorems.Thm_Eden_descending_antitone
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_one
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_one
import Theorems.Thm_Eden_spectrumInterpolation_nonneg_iff


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d} 3 := by
  have ha : Antitone (![2, 0, -2, -2, -c] : Fin 5 → ℝ) := by
    rw [← descending_radiusPairSpectrum_zero_one hc]
    exact descending_antitone _
  have hiff (d : ℝ) (hd : d ∈ Icc 0 5) :
      0 ≤ periodicGlobalGrowthInterpolation c d ↔ d ≤ 3 := by
    rw [periodicGlobalGrowthInterpolation_eq hc, spectrumInterpolation_nonneg_iff ha hd,
      kaplanYorkeDimension_zero_one hc]
  constructor
  · exact ⟨by norm_num, (hiff 3 (by norm_num)).mpr le_rfl⟩
  · intro d hd
    exact (hiff d hd.1).mp hd.2
end Eden
