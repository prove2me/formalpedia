-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.gram_det_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:42.612294+00:00
-- url     : https://prove2.me/submissions/b07cf79d-882d-4d8d-abab-8000cd280be8

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
import Theorems.Thm_Formalism_HN_HeightGram_norm_det_gramPl


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
theorem _root_.solution {d m : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin m → Fin d → K) :
    (gram X v e).det = (((gram X v e).det.re : ℝ) : ℂ) := by
  have h := Formalism.HN.HeightGram.norm_det_gramPl (Pi.basisFun K (Fin d)) X v e
  have hg : gram X v e = Formalism.HN.gramPl (Pi.basisFun K (Fin d)) X v e := rfl
  rw [← hg] at h
  have him : (gram X v e).det.im = 0 := by
    rw [← Complex.abs_re_eq_norm, h, abs_of_nonneg]
    rw [← h]; exact norm_nonneg _
  exact Complex.ext (by simp) (by simp [him])
end Formalism.DivisionValues.StepBAux
