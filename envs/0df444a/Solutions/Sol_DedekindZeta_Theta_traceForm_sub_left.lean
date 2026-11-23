-- Prove2me | solution 1 for DedekindZeta.Theta.traceForm_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:10:43.096788+00:00
-- url     : https://prove2.me/submissions/d14ace68-7823-4b46-accc-fd338ccb2a0e

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
theorem _root_.solution (η η' : mixedSpace K) (a : K) :
    traceForm K (η - η') a = traceForm K η a - traceForm K η' a := by
  simp only [traceForm, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul, Complex.sub_re,
    Finset.sum_sub_distrib]
  ring
end DedekindZeta.Theta
