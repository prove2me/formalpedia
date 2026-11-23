-- Prove2me | solution 1 for DedekindZeta.Theta.mixedGaussian_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:13.016638+00:00
-- url     : https://prove2.me/submissions/36450d48-f10f-4c5a-a7ed-6499612302ab

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
theorem _root_.solution : mixedGaussian K 0 = 1 := by
  rw [mixedGaussian, Finset.sum_eq_zero (fun w _ => by
    rw [show normAtPlace w (0 : mixedSpace K) = 0 from map_zero (normAtPlace w)]; ring),
    mul_zero, Real.exp_zero]
end DedekindZeta.Theta
