-- Prove2me | solution 1 for Eden.continuousOn_evolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:20:37.812347+00:00
-- url     : https://prove2.me/submissions/98cbcc92-8a58-4d30-9ce6-e91637f36b3f

import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_Uniqueness
import Theorems.Thm_Eden_hasDerivAt_evolution


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    ContinuousOn (fun t => evolution c t p) (Ici 0) :=
  fun _ ht => (hasDerivAt_evolution c ht p).continuousAt.continuousWithinAt
end Eden
