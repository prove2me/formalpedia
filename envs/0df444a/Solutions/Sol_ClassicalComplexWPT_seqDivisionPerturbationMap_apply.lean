-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivisionPerturbationMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:48.09222+00:00
-- url     : https://prove2.me/submissions/8bcca63d-25a6-46d3-98c1-dd8bdde72658

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p : L1Coeff ℕ) :
    seqDivisionPerturbationMap d p = seqDivisionPerturbation d p := rfl
end ClassicalComplexWPT
