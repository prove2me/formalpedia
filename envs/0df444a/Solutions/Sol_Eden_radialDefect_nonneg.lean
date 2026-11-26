-- Prove2me | solution 1 for Eden.radialDefect_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:37.272087+00:00
-- url     : https://prove2.me/submissions/4c0641ef-b4c5-4160-8fed-3d4ae75b47fe

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) : 0 ≤ radialDefect t s :=
  intervalIntegral.integral_nonneg_of_forall ht (fun _ => sq_nonneg _)
end Eden
