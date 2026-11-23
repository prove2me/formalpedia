-- Prove2me | solution 1 for Formalism.L2.Indef.sum_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:43.258004+00:00
-- url     : https://prove2.me/submissions/fe6870b3-9635-4581-87e1-5e2e7282e84e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef
theorem _root_.solution {F V Ix : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype Ix] (A : Ix → Submodule F V) (hi : iSupIndep A) (ht : (⨆ p, A p) = ⊤) :
    ∑ p, finrank F (A p) = finrank F V := by
  classical
  have hint : DirectSum.IsInternal A := by
    first
    | exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi ht
    | exact DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top hi ht
  rw [Module.finrank_eq_card_basis (hint.collectedBasis fun p => Module.finBasis F (A p)),
    Fintype.card_sigma]
  simp
end Formalism.L2.Indef
