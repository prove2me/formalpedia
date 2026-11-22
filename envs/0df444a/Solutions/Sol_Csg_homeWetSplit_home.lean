-- Prove2me | solution 1 for Csg.homeWetSplit_home
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:56:08.745885+00:00
-- url     : https://prove2.me/submissions/4152b93c-12b2-4714-9224-a56582e37523

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .home = ENNReal.ofReal p := rfl
end Csg
