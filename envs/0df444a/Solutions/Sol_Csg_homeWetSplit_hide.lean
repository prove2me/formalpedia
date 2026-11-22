-- Prove2me | solution 1 for Csg.homeWetSplit_hide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:56:52.002431+00:00
-- url     : https://prove2.me/submissions/8d68e86a-7c03-47bd-8c87-28e73eee4e53

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .hide = 0 := rfl
end Csg
