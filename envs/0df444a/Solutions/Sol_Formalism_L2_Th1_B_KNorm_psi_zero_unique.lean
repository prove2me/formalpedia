-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.psi_zero_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:51.352119+00:00
-- url     : https://prove2.me/submissions/2d2bb19e-6e6a-4494-937d-538a677ff41c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nadd_lt
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_ndom
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_n4
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_four_add_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key


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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {b2 b4 b6 b8 x : K}
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution (h2 : ‖(2 : K)‖ = 2⁻¹) (hb2 : ‖b2‖ ≤ 1) (hb4 : ‖b4‖ ≤ 1) (hb6 : ‖b6‖ ≤ 1)
    {x' : K} (hx : ‖x‖ = 4) (hx' : ‖x'‖ = 4)
    (h0 : 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0)
    (h0' : 4 * x' ^ 3 + b2 * x' ^ 2 + 2 * b4 * x' + b6 = 0) : x = x' := by
  have f := four_add_le h2 hb4 hb6 hx h0
  have f' := four_add_le h2 hb4 hb6 hx' h0'
  have hfac : (x - x') * (4 * x * x' + (x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4)) = 0 := by
    linear_combination h0 - h0'
  rcases mul_eq_zero.1 hfac with h | h
  · exact sub_eq_zero.1 h
  exfalso
  have hdom : ‖4 * x * x'‖ = 4 := by
    rw [norm_mul, norm_mul, n4 h2, hx, hx']
    norm_num
  have a1 : ‖x * (4 * x + b2)‖ < 4 := by
    rw [norm_mul, hx]
    linarith
  have a2 : ‖x' * (4 * x' + b2)‖ < 4 := by
    rw [norm_mul, hx']
    linarith
  have a3 : ‖2 * b4‖ < 4 := by
    rw [norm_mul, h2]
    nlinarith [norm_nonneg b4]
  have hr : ‖x * (4 * x + b2) + x' * (4 * x' + b2) + 2 * b4‖ < ‖4 * x * x'‖ := by
    rw [hdom]
    exact nadd_lt (nadd_lt a1 a2) a3
  have key := ndom hr
  rw [h, norm_zero, hdom] at key
  norm_num at key
end Formalism.L2.Th1.B.KNorm
