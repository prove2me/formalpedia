-- Prove2me | solution 1 for DedekindZeta.Theta.traceFormLin_mixedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:08:26.321727+00:00
-- url     : https://prove2.me/submissions/3dd49ed9-08c0-4eb8-a0d9-10ff77217d2f

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
theorem _root_.solution (η : mixedSpace K) (a : K) :
    traceFormLin K η (mixedEmbedding K a) = traceForm K η a := rfl
end DedekindZeta.Theta
