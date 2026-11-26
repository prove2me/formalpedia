-- Prove2me | solution 1 for Eden.asymptoticDimension_on_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:55.762797+00:00
-- url     : https://prove2.me/submissions/6e4b228a-64b0-426f-bfe3-610e4b503bcf

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_asymptoticDimension_eq_target_iff
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ torus) : asymptoticDimension c p = 4 + 4 / c :=
  (asymptoticDimension_eq_target_iff hc (torus_subset_attractor hp)).mpr hp
end Eden
