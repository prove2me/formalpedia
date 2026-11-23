-- Prove2me | solution 1 for DedekindZeta.Theta.gaussVSchwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:50:15.455157+00:00
-- url     : https://prove2.me/submissions/f5de80ed-25e7-4f33-997f-2f37d61560d5

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
theorem _root_.solution (v : minkowskiSpace K) :
    gaussVSchwartz K v = gaussV K v := rfl
end DedekindZeta.Theta
