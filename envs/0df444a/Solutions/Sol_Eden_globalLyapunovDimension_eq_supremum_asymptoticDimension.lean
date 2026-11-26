-- Prove2me | solution 1 for Eden.globalLyapunovDimension_eq_supremum_asymptoticDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:08.528866+00:00
-- url     : https://prove2.me/submissions/60c822ad-0a7d-41fc-bc38-964aada949f1

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_supremum_asymptoticDimension_attractor
import Theorems.Thm_Eden_globalLyapunovDimension_attractor


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    globalLyapunovDimension c attractor = sSup (asymptoticDimension c '' attractor) := by
  rw [globalLyapunovDimension_attractor hc, supremum_asymptoticDimension_attractor hc]
  rfl
end Eden
