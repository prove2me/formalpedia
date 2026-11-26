-- Prove2me | solution 1 for Eden.finiteTimeDimension_lt_target_of_not_mem_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:03.019794+00:00
-- url     : https://prove2.me/submissions/a0e202ad-5d59-4e5c-9b70-6260f7639a32

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_finiteTimeDimension_le_target
import Theorems.Thm_Eden_finiteTimeDimension_eq_target_iff

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) (hT : p ∉ torus) :
    finiteTimeDimension c t p < targetDimension c :=
  lt_of_le_of_ne (finiteTimeDimension_le_target hc ht hp)
    (fun heq => hT ((finiteTimeDimension_eq_target_iff hc ht hp).1 heq))
end Eden
