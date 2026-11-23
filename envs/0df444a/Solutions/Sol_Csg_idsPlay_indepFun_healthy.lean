-- Prove2me | solution 1 for Csg.idsPlay_indepFun_healthy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:58:14.755272+00:00
-- url     : https://prove2.me/submissions/261e7519-c5b9-4a7c-a256-67c5d7c07462

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_IntrusionDetectionRecurrence
import Theorems.Thm_Csg_idsRoundHealthy_measurable

set_option autoImplicit true
open Csg
open MeasureTheory Measure ProbabilityTheory
variable (q : ℕ → PMF AttackAction)
namespace Csg
theorem _root_.solution :
    iIndepFun (fun n (ω : ℕ → PolicyAction × AttackAction) => idsRoundHealthy (ω n))
      (idsPlayMeasure q) :=
  iIndepFun_infinitePi (X := fun (_ : ℕ) => idsRoundHealthy) fun _ => idsRoundHealthy_measurable
end Csg
