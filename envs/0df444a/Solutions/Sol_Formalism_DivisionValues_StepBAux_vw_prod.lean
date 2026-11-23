-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.vw_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:32.689856+00:00
-- url     : https://prove2.me/submissions/0c024578-2c69-4dad-8068-e0de275f8580

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep

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
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution (hV : ValBasic) (w : HeightOneSpectrum (𝓞 K)) {J : Type} (s : Finset J)
    (a : J → K) (ha : ∀ j, a j ≠ 0) : vw w (∏ j ∈ s, a j) = ∑ j ∈ s, vw w (a j) := by
  classical
  obtain ⟨hmul, -, -, -, h1, -, -⟩ := hV K w
  induction s using Finset.induction_on with
  | empty => simp [h1]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      hmul _ _ (ha j) (Finset.prod_ne_zero_iff.mpr fun i _ => ha i), ih]
end Formalism.DivisionValues.StepBAux
