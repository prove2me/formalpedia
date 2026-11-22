-- Prove2me | solution 1 for Csg.idsRoundHealthy_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:55:19.077648+00:00
-- url     : https://prove2.me/submissions/8593a9f3-1393-480b-a674-cae3d1eee255

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_IntrusionDetectionRecurrence

set_option autoImplicit true
open Csg
open MeasureTheory Measure ProbabilityTheory
variable (q : ℕ → PMF AttackAction)
namespace Csg
theorem _root_.solution : Measurable idsRoundHealthy :=
  Measurable.of_discrete
end Csg
