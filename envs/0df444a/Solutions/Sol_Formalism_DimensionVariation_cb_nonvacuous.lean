-- Prove2me | solution 1 for Formalism.DimensionVariation.cb_nonvacuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:19:37.585959+00:00
-- url     : https://prove2.me/submissions/fc3d5201-5f28-4af1-8031-d9c9d66451db

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_cbHyp_matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution :
    CBHyp (K := ℚ) (m := 2) (c := fun _ => 2) (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) (fun _ => 1)
      (AA := fun _ => Fin 2) (fun _ _ => Unit) (fun _ _ => ℂ) (fun _ _ => 1) (fun _ _ x p => x p.1)
      (fun _ _ _ _ => 1)
      (fun _ v p q => (v.embedding ((1 : Matrix (Fin 2) (Fin 2) ℚ) q.1 p.1)) • ContinuousLinearMap.id ℂ ℂ)
      (fun _ => 1) (fun _ _ => 1) ∧
    chainMat (R := ℚ) (m := 2) (c := fun _ => 2) (fun _ => 1) (Fin.last 2) ≠ 0 := by
  refine ⟨cbHyp_matrix ℚ 2 (fun _ => 2) (fun _ => 1) (fun _ _ => 1) (fun _ _ => zero_le_one) ?_, ?_⟩
  · intro j v q p
    by_cases h : q = p <;> simp [Matrix.one_apply, h]
  · show (1 : Matrix (Fin 2) (Fin 2) ℚ) * ((1 : Matrix (Fin 2) (Fin 2) ℚ) * 1) ≠ 0
    simp
end Formalism.DimensionVariation
