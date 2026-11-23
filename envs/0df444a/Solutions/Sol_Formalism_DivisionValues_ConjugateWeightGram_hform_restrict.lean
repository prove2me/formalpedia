-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.hform_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:25.726169+00:00
-- url     : https://prove2.me/submissions/9d5c7bd6-a858-4036-bd53-57d5d5958c71

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_comb_eq
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_gramMat_eq
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_eq_dot


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
theorem _root_.solution {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (z : Fin d → Fin n → K)
    (x y : Fin d → K) : hform (gramMat H z) x y = hform H (comb z x) (comb z y) := by
  rw [RationalHermitianForm.hform_eq_dot, RationalHermitianForm.hform_eq_dot, comb_eq, comb_eq, gramMat_eq,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
end Formalism.DivisionValues.ConjugateWeightGram
