-- Prove2me | solution 1 for Eden.planarAmplitude_parameter_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:31.988301+00:00
-- url     : https://prove2.me/submissions/8f29a40b-d69a-4df3-b287-8208c0f2b379

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
import Theorems.Thm_Eden_contDiff_amplitudeSq
import Theorems.Thm_Eden_amplitudeSq_parameter_identity
import Theorems.Thm_Eden_amplitudeSq_pos
import Theorems.Thm_Eden_planarAmplitude_pos
import Theorems.Thm_Eden_planarAmplitude_sq
import Theorems.Thm_Eden_sqrt_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s + 2 * s * deriv (planarAmplitude t) s =
      radialAmplitude t s := by
  have hB := ((contDiff_amplitudeSq ht 1).differentiable one_ne_zero s).hasDerivAt
  have hg := hB.sqrt (ne_of_gt (amplitudeSq_pos ht hs))
  have hd : deriv (planarAmplitude t) s =
      deriv (amplitudeSq t) s / (2 * planarAmplitude t s) := hg.deriv
  have hp := planarAmplitude_pos ht hs
  have hR := sqrt_radialDiscriminant_pos ht s
  have hsq := planarAmplitude_sq ht hs
  have hrel := amplitudeSq_parameter_identity ht s
  rw [hd]
  unfold radialAmplitude
  field_simp [ne_of_gt hp, ne_of_gt hR] at hrel ⊢
  nlinarith [congrArg (fun x : ℝ => x * Real.sqrt (radialDiscriminant t s) ^ 3) hsq]
end Eden
