-- Prove2me | solution 1 for DedekindZeta.Theta.norm_unitSMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:52:22.660509+00:00
-- url     : https://prove2.me/submissions/e348ec00-ba89-4936-b854-6a9b549c7db0

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
theorem _root_.solution (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x :=
  norm_unit_smul u x
end DedekindZeta.Theta
