-- Prove2me | solution 1 for DedekindZeta.Theta.traceForm_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:11:35.040805+00:00
-- url     : https://prove2.me/submissions/0bf3822d-3ecd-4745-96c3-7497564afd53

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_traceFormLin_mixedEmbedding

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (η : mixedSpace K) (n : ℕ) (a : K) :
    traceForm K η ((n : K) * a) = n * traceForm K η a := by
  rw [← traceFormLin_mixedEmbedding, ← nsmul_eq_mul, map_nsmul, map_nsmul,
    traceFormLin_mixedEmbedding, nsmul_eq_mul]
end DedekindZeta.Theta
