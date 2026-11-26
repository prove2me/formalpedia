-- Prove2me | solution 1 for Eden.continuousOn_frequencyEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:41.421365+00:00
-- url     : https://prove2.me/submissions/00925ce5-8e35-41a9-9704-07978daa4703

import Definitions.Def_Eden_FrequencyEvolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_FrequencyUniqueness
import Theorems.Thm_Eden_hasDerivAt_frequencyEvolution


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) (p : PhaseSpace) :
    ContinuousOn (fun t => frequencyEvolution c ν t p) (Ici 0) :=
  fun _ ht => (hasDerivAt_frequencyEvolution c ν ht p).continuousAt.continuousWithinAt
end Eden
