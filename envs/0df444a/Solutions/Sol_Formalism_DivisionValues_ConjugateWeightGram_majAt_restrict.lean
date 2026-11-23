-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.majAt_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:25.763672+00:00
-- url     : https://prove2.me/submissions/cbb161d0-d84d-4155-8bae-ab9915e03aa1

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_comb_eq
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
theorem _root_.solution {K0 : Subfield K} {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hH : IsRatHerm K0 H X)
    (z : Fin d → Fin n → K) (XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (hXT : ((XT v)⁻¹)ᴴ * (XT v)⁻¹ =
      ((colMat z).map v.embedding)ᴴ * (H.map v.embedding) * (colMat z).map v.embedding)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (comb z x) (comb z y) := by
  rw [StepBAux.majAt_eq, StepBAux.majAt_eq]
  have hm1 : met XT v =
      ((colMat z).map v.embedding)ᴴ * (H.map v.embedding) * (colMat z).map v.embedding := hXT
  have hm2 : met X v = H.map v.embedding := (hH.2 v).2
  have hc : ∀ u : Fin d → K, cvec v.embedding (comb z u) =
      ((colMat z).map v.embedding).mulVec (cvec v.embedding u) := by
    intro u
    funext i
    simp [cvec, comb_eq, Matrix.mulVec, dotProduct]
  rw [hm1, hm2, hc, hc, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
end Formalism.DivisionValues.ConjugateWeightGram
