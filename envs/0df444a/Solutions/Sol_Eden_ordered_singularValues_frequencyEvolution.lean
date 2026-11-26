-- Prove2me | solution 1 for Eden.ordered_singularValues_frequencyEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:52.420106+00:00
-- url     : https://prove2.me/submissions/4dd1cd38-b841-4749-8786-393f5eaace49

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
import Theorems.Thm_Eden_singularValues_fderiv_frequencyEvolution
import Theorems.Thm_Eden_antitone_eq_of_multiset_eq
import Theorems.Thm_Eden_singularValues_fderiv_evolution


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fun i : Fin 5 => (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i := by
  apply antitone_eq_of_multiset_eq
  · exact fun i j hij => (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues_antitone hij
  · exact fun i j hij => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues_antitone hij
  · exact (singularValues_fderiv_frequencyEvolution c ν ht p).trans
      (singularValues_fderiv_evolution c ht p).symm
end Eden
