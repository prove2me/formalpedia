-- Prove2me | solution 1 for ClassicalComplexWPT.L1Coeff.embed_apply_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:22.079238+00:00
-- url     : https://prove2.me/submissions/8931a88a-9d5b-4863-80d8-ed9674223c73

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
open ClassicalComplexWPT.L1Coeff
variable {I J : Type*}
namespace ClassicalComplexWPT.L1Coeff
theorem _root_.solution (e : I ↪ J) (f : L1Coeff I) (j : J)
    (hj : j ∉ Set.range e) : embed e f j = 0 := embedFun_apply_of_not_mem e f j hj
end ClassicalComplexWPT.L1Coeff
