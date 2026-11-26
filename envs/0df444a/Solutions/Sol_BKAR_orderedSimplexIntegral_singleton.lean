-- Prove2me | solution 1 for BKAR.orderedSimplexIntegral_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:55.788464+00:00
-- url     : https://prove2.me/submissions/17875208-b0eb-4e46-8c43-8fb751003592

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (e : Edge V) (f : List ℝ → ℝ) :
    orderedSimplexIntegral [e] f = ∫ t in 0..(1 : ℝ), f [t] :=
  rfl
end BKAR
