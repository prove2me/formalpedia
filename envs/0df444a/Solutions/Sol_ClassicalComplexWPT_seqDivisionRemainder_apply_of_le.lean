-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivisionRemainder_apply_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:55.926996+00:00
-- url     : https://prove2.me/submissions/f3d3dab9-159d-4be7-8fe9-9f82b8128277

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
theorem _root_.solution (d : ℕ) (p : L1Coeff ℕ)
    (hp : ‖p‖ < 1) (f : L1Coeff ℕ) {n : ℕ} (hn : d ≤ n) :
    seqDivisionRemainder d p hp f n = 0 := seqLowCut_apply_of_le d _ hn
end ClassicalComplexWPT
