-- Prove2me | solution 1 for Formalism.DivisionValues.Rb.Qd_place
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:12.126999+00:00
-- url     : https://prove2.me/submissions/7e57a8aa-56a1-4600-9ea0-b6f544bc5b7c

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
theorem _root_.solution {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ : IsQuotMetric P H XQ)
    (u : InfinitePlace K) : Qd P H u.embedding = ((metMat XQ u).det)⁻¹ := by
  have hm : metMat XQ u =
      ((P.map u.embedding) * (H.map u.embedding)⁻¹ * (P.map u.embedding)ᴴ)⁻¹ := (hXQ u).2
  rw [hm, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_inv]
  rfl
end Formalism.DivisionValues.Rb
