-- Prove2me | solution 1 for Eden.asymptoticDimension_lt_target_of_not_mem_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:10.329188+00:00
-- url     : https://prove2.me/submissions/16c7a8c3-2742-400f-b317-2baff49d7bbc

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
import Theorems.Thm_Eden_asymptoticDimension_le_target
import Theorems.Thm_Eden_asymptoticDimension_eq_target_iff

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus) :
    asymptoticDimension c p < targetDimension c :=
  lt_of_le_of_ne (asymptoticDimension_le_target hc p)
    (fun h => hT ((asymptoticDimension_eq_target_iff hc hp).mp h))
end Eden
