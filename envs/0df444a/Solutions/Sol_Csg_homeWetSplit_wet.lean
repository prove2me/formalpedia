-- Prove2me | solution 1 for Csg.homeWetSplit_wet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:56:35.426198+00:00
-- url     : https://prove2.me/submissions/390231e6-9d21-4be2-a4a3-9c6ad6908206

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .wet = ENNReal.ofReal (1 - p) := rfl
end Csg
