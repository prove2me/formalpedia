-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.zLin_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:32:34.528684+00:00
-- url     : https://prove2.me/submissions/79ba38bb-b542-438e-889f-3ab1a42e51a6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_endInt_natCast
import Theorems.Thm_Formalism_L2_Th1_C_Clo_addDefect_zero_right
import Theorems.Thm_Formalism_L2_Th1_C_Clo_addDefect_add_right
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_add
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_one
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_zero_left
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fmul
import Theorems.Thm_Formalism_L2_Th1_C_lGSubgroup


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Clo
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {R : Subring K} {l linv : PowerSeries K}
variable [CharZero K] {ph : PowerSeries K} {σ : Type}
namespace Formalism.L2.Th1.C.Clo
theorem _root_.solution (h : Frame R l linv ph) (h1 : F1 R l linv ph) {x y : MvPowerSeries σ K}
    (hx : IsPt R x) (hy : IsPt R y) (n : ℕ) :
    LG R (be0 l linv ph x (fmul l linv (n : K) y) - (n : K) • be0 l linv ph x y) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, Pts.fmul_zero_left h.1, addDefect_zero_right h hx.1, zero_smul, sub_zero]
    exact (lGSubgroup K R σ).1
  | succ n ih =>
    have hp := addDefect_add_right h1 hx (Pts.isPt_fmul h.1 (endInt_natCast h.1 h.2.1 n) hy) hy
    have := (lGSubgroup K R σ).2.1 _ _ hp ih
    rw [Nat.cast_succ, Pts.fmul_add h.1 _ _ hy.1, Pts.fmul_one h.1 hy.1, add_smul, one_smul]
    convert this using 1
    abel
end Formalism.L2.Th1.C.Clo
