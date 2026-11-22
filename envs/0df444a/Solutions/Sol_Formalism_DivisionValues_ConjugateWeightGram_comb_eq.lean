-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.comb_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:56.157892+00:00
-- url     : https://prove2.me/submissions/cc625d3e-aac9-4a57-a164-859273968efe

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
theorem _root_.solution {n d : ℕ} (z : Fin d → Fin n → K) (x : Fin d → K) :
    comb z x = (colMat z).mulVec x := by
  funext i
  simp [comb, colMat, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
end Formalism.DivisionValues.ConjugateWeightGram
