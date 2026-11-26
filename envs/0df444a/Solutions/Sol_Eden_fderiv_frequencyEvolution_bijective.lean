-- Prove2me | solution 1 for Eden.fderiv_frequencyEvolution_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:58.017503+00:00
-- url     : https://prove2.me/submissions/03524f0c-3ca7-4ac8-b15c-e3289fcb9908

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
import Theorems.Thm_Eden_fderiv_evolution_bijective
import Theorems.Thm_Eden_fderiv_frequencyEvolution


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) : Function.Bijective (fderiv ℝ (frequencyEvolution c ν t) p) := by
  rw [fderiv_frequencyEvolution c ν ht]
  exact (frequencyCorrection ν t).bijective.comp (fderiv_evolution_bijective c ht p)
end Eden
