-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.sgStar_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:14.62802+00:00
-- url     : https://prove2.me/submissions/5b65fb22-c253-498b-a0ec-c827b0fe9a41

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_sigma_scale
import Theorems.Thm_Formalism_L2_Th1_B_Sq_rescale_fExp


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
open Formalism.L2.Th1.CM (cW wpNum wpDen uSer)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Scale
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.F.Scale
theorem _root_.solution (s lam : K) (P : PowerSeries K) :
    C lam * Formalism.L2.Th1.B.sgStar (lam ^ 2 * s) (C (lam ^ 2) * rescale lam P)
      = rescale lam (Formalism.L2.Th1.B.sgStar s P) := by
  unfold Formalism.L2.Th1.B.sgStar
  rw [map_mul, ← sigma_scale, Formalism.L2.Th1.B.Sq.rescale_fExp lam (by simp), mul_assoc]
  congr 3
  rw [map_neg, map_mul, map_pow, rescale_X, mul_pow, ← map_pow, ← mul_assoc]
  congr 2
  have hC : rescale lam (C (s / 2)) = C (s / 2) := by
    ext n
    rw [coeff_rescale, coeff_C]
    split_ifs with h0
    · subst h0; rw [pow_zero, one_mul]
    · rw [mul_zero]
  rw [hC, ← map_mul]
  congr 1
  ring
end Formalism.L2.Th1.F.Scale
