-- Prove2me | solution 1 for Formalism.CountingSumsFrames.mat_comm_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:54.790147+00:00
-- url     : https://prove2.me/submissions/d24bdf78-edfd-4b60-983e-0314ee61578a

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] {m : ℕ} (X Y : Matrix (Fin m) (Fin m) O) (c : O)
    (hc : c ≠ 0) (h : X * Y = c • (1 : Matrix (Fin m) (Fin m) O)) : Y * X = c • (1 : Matrix (Fin m) (Fin m) O) := by
  have hdet : X.det * Y.det = c ^ m := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hX : X.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero m hc hdet.symm
  have h2 : X * (Y * X - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, sub_self]
  have h3 : X.det • (Y * X - c • 1) = 0 := by
    calc X.det • (Y * X - c • 1) = (X.adjugate * X) * (Y * X - c • 1) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = X.adjugate * (X * (Y * X - c • 1)) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [h2, Matrix.mul_zero]
  ext i j
  have h4 := congrFun (congrFun h3 i) j
  rw [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul, mul_eq_zero] at h4
  have h5 := h4.resolve_left hX
  rw [Matrix.sub_apply, sub_eq_zero] at h5
  exact h5
end Formalism.CountingSumsFrames
