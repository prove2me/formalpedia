-- Prove2me | solution 1 for ClassicalComplexWPT.norm_convolutionRight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:04.946808+00:00
-- url     : https://prove2.me/submissions/96fa8217-4545-4b5a-981b-087184ae3eae

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_ClassicalComplexWPT_WeightedSeries

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution (g : L1Coeff A) : ‖convolutionRight g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖convolution f g‖ ≤ ‖g‖ * ‖f‖
  simpa [mul_comm] using norm_convolution_le f g
end ClassicalComplexWPT
