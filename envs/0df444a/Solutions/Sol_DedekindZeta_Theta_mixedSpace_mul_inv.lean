-- Prove2me | solution 1 for DedekindZeta.Theta.mixedSpace_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:36.963232+00:00
-- url     : https://prove2.me/submissions/107f0b69-ea03-4446-8ca1-e9efa564f208

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
theorem _root_.solution (a b : mixedEmbedding.mixedSpace K) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  apply Prod.ext <;> funext i <;> simp [Pi.inv_apply, mul_inv_rev, mul_comm]
end DedekindZeta.Theta
