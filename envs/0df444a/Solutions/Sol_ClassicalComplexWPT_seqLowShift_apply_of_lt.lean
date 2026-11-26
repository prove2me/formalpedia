-- Prove2me | solution 1 for ClassicalComplexWPT.seqLowShift_apply_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:58.231342+00:00
-- url     : https://prove2.me/submissions/f0433ee7-42dc-4f46-8b44-8bc9365e443f

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_L1Coeff_embed_apply_of_not_mem

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : n < d) :
    seqLowShift d f n = 0 := by
  apply L1Coeff.embed_apply_of_not_mem
  rintro ⟨m, hm⟩
  change m + d = n at hm
  omega
end ClassicalComplexWPT
