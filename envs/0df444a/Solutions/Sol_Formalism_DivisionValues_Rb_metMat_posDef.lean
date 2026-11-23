-- Prove2me | solution 1 for Formalism.DivisionValues.Rb.metMat_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:15.288331+00:00
-- url     : https://prove2.me/submissions/77590e87-76fc-4610-a6ff-f9c96334b3ed

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaSecond

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
open Formalism.DivisionValues.Rb
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.Rb
theorem _root_.solution {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (hX : IsUnit (X v).det) : (metMat X v).PosDef := by
  unfold metMat
  apply Matrix.PosDef.conjTranspose_mul_self
  exact Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ hX))
end Formalism.DivisionValues.Rb
