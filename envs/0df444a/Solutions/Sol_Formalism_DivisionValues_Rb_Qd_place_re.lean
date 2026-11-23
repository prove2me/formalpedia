-- Prove2me | solution 1 for Formalism.DivisionValues.Rb.Qd_place_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:38.623766+00:00
-- url     : https://prove2.me/submissions/ff24b8fe-4f10-4544-9308-28ee6d3a2033

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
import Theorems.Thm_Formalism_DivisionValues_Rb_metMat_posDef
import Theorems.Thm_Formalism_DivisionValues_Rb_pos_real
import Theorems.Thm_Formalism_DivisionValues_Rb_Qd_place

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
    (u : InfinitePlace K) :
    (Qd P H u.embedding).re = ((metMat XQ u).det.re)⁻¹ ∧ 0 < (metMat XQ u).det.re := by
  obtain ⟨hz, hr⟩ := pos_real (metMat_posDef XQ u (hXQ u).1).det_pos
  refine ⟨?_, hr⟩
  have e : ((metMat XQ u).det)⁻¹ = ((((metMat XQ u).det.re)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, ← hz]
  rw [Qd_place P H XQ hXQ u, e, Complex.ofReal_re]
end Formalism.DivisionValues.Rb
