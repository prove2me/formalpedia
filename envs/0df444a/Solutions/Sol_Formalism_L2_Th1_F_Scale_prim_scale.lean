-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.prim_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:21.654045+00:00
-- url     : https://prove2.me/submissions/2aadc20d-a522-45a7-99de-c08d1b248b00

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale

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
theorem _root_.solution (lam : K) (f : PowerSeries K) :
    Formalism.L2.Th1.B.prim (C lam * rescale lam f) = rescale lam (Formalism.L2.Th1.B.prim f) := by
  ext n
  rw [coeff_rescale]
  unfold Formalism.L2.Th1.B.prim
  rw [coeff_mk, coeff_mk]
  split_ifs with h0
  · rw [mul_zero]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [Nat.succ_sub_one, coeff_C_mul, coeff_rescale, pow_succ]
    ring
end Formalism.L2.Th1.F.Scale
