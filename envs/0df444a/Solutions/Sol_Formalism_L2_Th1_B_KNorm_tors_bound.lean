-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.tors_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:42.049528+00:00
-- url     : https://prove2.me/submissions/af4ac78c-411c-4627-9469-b0d63fda4d9f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_two_tors_le
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_dup_big

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KNorm
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)
variable {K : Type} [NormedField K] [IsUltrametricDist K] [DecidableEq K]
  {W : WeierstrassCurve K}
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution (hW : IntCurve W) (h2 : ‖(2 : K)‖ = 2⁻¹) (P : W.toAffine.Point) (k : ℕ)
    (hk : (2 ^ k) • P = 0) (hP : P + P ≠ 0) : ‖px W P‖ < 4 := by
  by_contra hge
  push_neg at hge
  have claim : ∀ j : ℕ, 4 < ‖px W ((2 ^ (j + 1)) • P)‖ := by
    intro j
    induction j with
    | zero =>
      rw [zero_add, pow_one, two_nsmul]
      exact dup_big hW h2 P hge hP
    | succ j ih =>
      have hQ : (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P ≠ 0 := by
        intro e
        have := two_tors_le hW h2 _ e
        linarith
      have e : (2 ^ (j + 1 + 1)) • P = (2 ^ (j + 1)) • P + (2 ^ (j + 1)) • P := by
        rw [← add_nsmul]
        congr 1
        ring
      rw [e]
      exact dup_big hW h2 _ ih.le hQ
  cases k with
  | zero =>
    rw [pow_zero, one_nsmul] at hk
    rw [hk, add_zero] at hP
    exact hP rfl
  | succ k =>
    have hc := claim k
    rw [hk] at hc
    change 4 < ‖(0 : K)‖ at hc
    rw [norm_zero] at hc
    norm_num at hc
end Formalism.L2.Th1.B.KNorm
