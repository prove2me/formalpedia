-- Prove2me | solution 1 for Formalism.DivisionValues.metMat_det_re_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:21.490206+00:00
-- url     : https://prove2.me/submissions/743943c1-137b-4265-914d-b0648ca04c85

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (hX : IsUnit (X v).det) : (metMat X v).det.re ≠ 0 := by
  have hY : ((X v)⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det (X v) hX).ne_zero
  have hm : (metMat X v).det = (Complex.normSq ((X v)⁻¹).det : ℂ) := by
    rw [metMat, Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hm, Complex.ofReal_re]
  exact (Complex.normSq_pos.mpr hY).ne'
end Formalism.DivisionValues
