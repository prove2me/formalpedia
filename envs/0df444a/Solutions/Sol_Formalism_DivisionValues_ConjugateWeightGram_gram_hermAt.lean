-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.gram_hermAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:23.098004+00:00
-- url     : https://prove2.me/submissions/b5ebcf19-3f95-4a83-89a5-963c146da6bf

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_StepBAux_majAt_eq
import Theorems.Thm_Formalism_DivisionValues_majAt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram
open StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ConjugateWeightGram
theorem _root_.solution {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v0 : InfinitePlace K) (hv0 : IsConjAt v0) (hH : IsHermAt v0 H X) (f : Fin d → Fin d → K) :
    (gram X v0 f).det = v0.embedding (gramR H f) := by
  have hm : met X v0 = H.map v0.embedding := hH.2
  rw [gramR, RingHom.map_det]
  congr 1
  ext a b
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, StepBAux.majAt_eq, hm, RingHom.mapMatrix_apply,
    Matrix.map_apply, dotProduct, Matrix.mulVec, cvec, Pi.star_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv0, Complex.star_def]
end Formalism.DivisionValues.ConjugateWeightGram
