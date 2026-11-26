-- Prove2me | solution 1 for Eden.finiteTimeDimension_on_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:10:52.973401+00:00
-- url     : https://prove2.me/submissions/42221ca4-a2ba-437e-b402-dba82215a0f5

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_finiteTimeDimension_eq_target_iff
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ torus) : finiteTimeDimension c t p = 4 + 4 / c :=
  (finiteTimeDimension_eq_target_iff hc ht (torus_subset_attractor hp)).2 hp
end Eden
