-- Prove2me | solution 1 for Eden.fderiv_frequencyEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:25.57694+00:00
-- url     : https://prove2.me/submissions/577a28e9-9bff-41bb-a40b-32f46727ea8a

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
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    fderiv ℝ (frequencyEvolution c ν t) p =
      (frequencyCorrection ν t).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (evolution c t) p) := by
  have he : frequencyEvolution c ν t = (frequencyCorrection ν t) ∘ evolution c t :=
    funext (frequencyEvolution_eq_correction c ν t)
  rw [he]
  exact ((frequencyCorrection ν t).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp p
    ((contDiff_evolution c ht 1).differentiable one_ne_zero p).hasFDerivAt).fderiv
end Eden
