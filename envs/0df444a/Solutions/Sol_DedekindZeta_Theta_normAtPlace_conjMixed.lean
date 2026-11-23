-- Prove2me | solution 1 for DedekindZeta.Theta.normAtPlace_conjMixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:41.497793+00:00
-- url     : https://prove2.me/submissions/1b369e31-9854-429a-8209-1d96d9f54140

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
theorem _root_.solution (w : InfinitePlace K) (ξ : mixedSpace K) :
    normAtPlace w (conjMixed K ξ) = normAtPlace w ξ := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, normAtPlace_apply_of_isReal hw, conjMixed_fst]
  · rw [normAtPlace_apply_of_isComplex hw, normAtPlace_apply_of_isComplex hw, conjMixed_snd,
      Complex.norm_conj]
end DedekindZeta.Theta
