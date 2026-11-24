-- Prove2me | solution 1 for Formalism.L2.Th1.B.invertedEven
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:21:59.661681+00:00
-- url     : https://prove2.me/submissions/68a2684c-e379-45a3-8f66-2a36e47dfff9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Theorems.Thm_Formalism_L2_Th1_B_invertedSecondDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
namespace Formalism.L2.Th1.B
theorem _root_.solution : WEven := by
  intro K _ _ A kap w hw
  obtain ⟨h1, h2⟩ := invertedSecondDeriv K A kap w hw
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨m, rfl⟩ := hn
  rcases m with _ | m
  · simpa using h1
  ·
    have hk : PowerSeries.coeff (2 * m + 1) w = 0 := ih _ (by omega) ⟨m, rfl⟩
    have hsq : PowerSeries.coeff (2 * m + 1) (w ^ 2) = 0 := by
      rw [pow_two, PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      simp only at hij
      rcases Nat.even_or_odd i with ⟨a, ha⟩ | hi
      · rw [ih j (by omega) ⟨m - a, by omega⟩, mul_zero]
      · rw [ih i (by omega) hi, zero_mul]
    have e : (2 + 4 * C A * w + 6 * C kap * w ^ 2 : PowerSeries K) =
        C 2 + C (4 * A) * w + C (6 * kap) * w ^ 2 := by
      simp only [map_mul, map_ofNat]
    have hc := congrArg (PowerSeries.coeff (2 * m + 1)) h2
    rw [e, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hk, hsq,
      PowerSeries.coeff_C, if_neg (by omega)] at hc
    simp only [dz, PowerSeries.coeff_derivative] at hc
    have a1 : ((2 * m + 1 + 1 : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    have a2 : ((2 * m + 1 : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    have hz : PowerSeries.coeff (2 * m + 1 + 1 + 1) w = 0 := by
      have hc' : PowerSeries.coeff (2 * m + 1 + 1 + 1) w * (((2 * m + 1 + 1 : ℕ) : K) + 1) *
          (((2 * m + 1 : ℕ) : K) + 1) = 0 := by
        rw [hc]
        ring
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hc').resolve_right a2)).resolve_right a1
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring]
    exact hz
end Formalism.L2.Th1.B
