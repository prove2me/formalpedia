-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.eq_zero_of_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:08.144241+00:00
-- url     : https://prove2.me/submissions/5bb8e95c-6ba6-454c-9133-22d8554db224

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
import Theorems.Thm_Formalism_L2_Th1_B_coeff_eq_zero_of_eval_second_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.SAdd
theorem _root_.solution {K : Type} [Field K] [CharZero K] {k : MvPowerSeries (Fin 2) K}
    (hk : pd 0 k = pd 1 k) (h0 : ev0 k = 0) : k = 0 := by
  have key : ∀ j : ℕ, ∀ n : Fin 2 →₀ ℕ, n 1 = j → MvPowerSeries.coeff n k = 0 := by
    intro j
    induction j with
    | zero => exact fun n hn => coeff_eq_zero_of_eval_second_zero h0 n hn
    | succ j ih =>
      intro n hn
      have hle : Finsupp.single (1 : Fin 2) 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      set m := n - Finsupp.single (1 : Fin 2) 1 with hm
      have hmn : m + Finsupp.single 1 1 = n := by
        rw [hm, tsub_add_cancel_of_le hle]
      have hm1 : m 1 = j := by simp [hm, hn]
      have e := congrArg (MvPowerSeries.coeff m) hk
      rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, hmn,
        ih (m + Finsupp.single 0 1) (by simp [hm1]), zero_mul] at e
      rcases mul_eq_zero.mp e.symm with h | h
      · exact h
      · exact absurd h (Nat.cast_add_one_ne_zero _)
  ext n
  rw [map_zero]
  exact key _ n rfl
end Formalism.L2.Th1.B.SAdd
