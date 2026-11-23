-- Prove2me | solution 1 for DedekindZeta.Theta.mixedEmbedding_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:56.582031+00:00
-- url     : https://prove2.me/submissions/b5119e94-ab86-4184-a5c2-6b67aa040628

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
theorem _root_.solution (y : K) :
    (mixedEmbedding K y)⁻¹ = mixedEmbedding K y⁻¹ := by
  apply Prod.ext <;> funext i <;> simp [Pi.inv_apply, map_inv₀]
end DedekindZeta.Theta
