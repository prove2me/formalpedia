-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.isHermAt_of_ratHerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:46:39.455302+00:00
-- url     : https://prove2.me/submissions/02a57c14-4afd-4871-b824-72d8b31e6e8c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral

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
theorem _root_.solution {K0 : Subfield K} {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (h : IsRatHerm K0 H X) (v0 : InfinitePlace K) :
    IsHermAt v0 H X :=
  ⟨fun v => (h.2 v).1, (h.2 v0).2⟩
end Formalism.DivisionValues.ConjugateWeightGram
