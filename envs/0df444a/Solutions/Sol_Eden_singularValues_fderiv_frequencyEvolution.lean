-- Prove2me | solution 1 for Eden.singularValues_fderiv_frequencyEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:05.676628+00:00
-- url     : https://prove2.me/submissions/582d0572-ed4b-419f-9d5c-9a64a5f0ba24

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
import Theorems.Thm_Eden_fderiv_frequencyEvolution_orthogonal
import Theorems.Thm_Eden_derivativeFactors_pos
import Theorems.Thm_Eden_singularValues_orthogonalDiagonalMap


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by
  rw [fderiv_frequencyEvolution_orthogonal c ν ht]
  exact singularValues_orthogonalDiagonalMap _ _ _
    (fun i => (derivativeFactors_pos c ht p i).le)
end Eden
