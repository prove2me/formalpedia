-- Prove2me | solution 1 for ClassicalComplexWPT.lowShift_apply_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:17.341889+00:00
-- url     : https://prove2.me/submissions/158309be-1926-4b9e-b922-a1f85d4a39e7

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
variable {A : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (f : L1Coeff (A × ℕ)) (a : A) {n : ℕ}
    (hn : n < d) : lowShift d f (a,n) = 0 := by
  apply L1Coeff.embed_apply_of_not_mem
  rintro ⟨⟨b,m⟩, h⟩
  change (b, m + d) = (a, n) at h
  have h' := congrArg Prod.snd h
  omega
end ClassicalComplexWPT
