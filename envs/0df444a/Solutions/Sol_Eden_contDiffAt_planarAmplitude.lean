-- Prove2me | solution 1 for Eden.contDiffAt_planarAmplitude
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:07.518382+00:00
-- url     : https://prove2.me/submissions/c685edcc-083c-4b8f-95d6-b19ddb44d1db

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
import Theorems.Thm_Eden_contDiff_amplitudeSq
import Theorems.Thm_Eden_amplitudeSq_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (planarAmplitude t) s :=
  (contDiff_amplitudeSq ht n).contDiffAt.sqrt (ne_of_gt (amplitudeSq_pos ht hs))
end Eden
