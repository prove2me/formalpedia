-- Prove2me | solution 1 for Formalism.L2.Indef.ColData.fnorm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:33.851523+00:00
-- url     : https://prove2.me/submissions/102e0017-d8c2-41c9-8244-2ce29b8473b2

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
open Formalism.L2.Indef.ColData
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {S : IndefData Df} (C : ColData Dc Sp S)
namespace Formalism.L2.Indef.ColData
theorem _root_.solution {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det) (y : Fin n → ℂ) (h : fnorm Y y = 0) : y = 0 := by
  have h1 : ∑ i, ‖(Y⁻¹.mulVec y) i‖ ^ 2 = 0 := by
    have h' : Real.sqrt (∑ i, ‖(Y⁻¹.mulVec y) i‖ ^ 2) = 0 := h
    rwa [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => by positivity)] at h'
  have h2 : Y⁻¹.mulVec y = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h1 i (Finset.mem_univ i)
    simpa using this
  calc y = (Y * Y⁻¹).mulVec y := by rw [Matrix.mul_nonsing_inv Y hY, Matrix.one_mulVec]
    _ = Y.mulVec (Y⁻¹.mulVec y) := (Matrix.mulVec_mulVec y Y Y⁻¹).symm
    _ = 0 := by rw [h2, Matrix.mulVec_zero]
end Formalism.L2.Indef.ColData
