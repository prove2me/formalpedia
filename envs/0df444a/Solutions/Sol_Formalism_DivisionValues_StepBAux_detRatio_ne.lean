-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.detRatio_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:04.375015+00:00
-- url     : https://prove2.me/submissions/9dbb5c17-b839-4c9e-9053-ef8af95e8670

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
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_re_ne
import Theorems.Thm_Formalism_DivisionValues_StepBAux_std_li
import Theorems.Thm_Formalism_DivisionValues_StepBAux_image_li

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
theorem _root_.solution [IsTotallyComplex K] {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hXS : ∀ v, IsUnit (XS v).det) (hXT : ∀ v, IsUnit (XT v).det)
    (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det) (v : InfinitePlace K) :
    detRatio XS XT φ v ≠ 0 :=
  div_ne_zero (gram_re_ne XT hXT _ (image_li φ hφ _ (std_li d)) v)
    (gram_re_ne XS hXS _ (std_li d) v)
end Formalism.DivisionValues.StepBAux
