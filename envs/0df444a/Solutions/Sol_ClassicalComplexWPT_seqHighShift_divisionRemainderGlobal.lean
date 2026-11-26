-- Prove2me | solution 1 for ClassicalComplexWPT.seqHighShift_divisionRemainderGlobal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:15.098286+00:00
-- url     : https://prove2.me/submissions/622e3deb-a351-4d07-b847-706473a42f70

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRemainderGlobal_eq
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainder
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero


attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainder

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ) (p f : L1Coeff ℕ)
    (hp : ‖p‖ < 1) :
    seqHighShift d (seqDivisionRemainderGlobal d (p,f)) = 0 := by
  rw [seqDivisionRemainderGlobal_eq d p f hp]
  exact seqHighShift_divisionRemainder d p hp f
end ClassicalComplexWPT
