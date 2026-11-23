-- Prove2me | solution 1 for DedekindZeta.Theta.continuous_mixedGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:54.787838+00:00
-- url     : https://prove2.me/submissions/3047b191-578b-4c6f-a93b-b1e40b81fef6

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution : Continuous (mixedGaussian K) := by
  unfold mixedGaussian
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  refine continuous_finset_sum _ (fun w _ => ?_)
  exact continuous_const.mul ((continuous_normAtPlace w).pow 2)
end DedekindZeta.Theta
