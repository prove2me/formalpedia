-- Prove2me | solution 1 for Eden.contDiff_frequencyEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:42.525464+00:00
-- url     : https://prove2.me/submissions/212b7953-8265-4f63-9ac6-9c5ba00e4583

import Definitions.Def_Eden_FrequencyEvolution
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FrequencyRotation
import Theorems.Thm_Eden_frequencyEvolution_eq_correction
import Theorems.Thm_Eden_contDiff_evolution


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (frequencyEvolution c ν t) := by
  have he : frequencyEvolution c ν t = (frequencyCorrection ν t) ∘ evolution c t :=
    funext (frequencyEvolution_eq_correction c ν t)
  rw [he]
  exact (frequencyCorrection ν t).toContinuousLinearEquiv.contDiff.comp (contDiff_evolution c ht n)
end Eden
