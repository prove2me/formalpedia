-- Prove2me | solution 1 for Eden.volumeDefect_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:26.120522+00:00
-- url     : https://prove2.me/submissions/5b9176dd-0af0-4b3d-9f05-b3eaa8d1369f

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
import Theorems.Thm_Eden_radialDefect_nonneg

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    0 ≤ volumeDefect t p :=
  add_nonneg (radialDefect_nonneg ht _) (radialDefect_nonneg ht _)
end Eden
