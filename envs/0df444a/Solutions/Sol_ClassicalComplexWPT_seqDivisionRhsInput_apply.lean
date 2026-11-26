-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivisionRhsInput_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:59.515485+00:00
-- url     : https://prove2.me/submissions/fa469ab3-9615-40ee-bbba-38f1f2859c34

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
theorem _root_.solution (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    seqDivisionRhsInput d pf = seqHighShift d pf.2 := rfl
end ClassicalComplexWPT
