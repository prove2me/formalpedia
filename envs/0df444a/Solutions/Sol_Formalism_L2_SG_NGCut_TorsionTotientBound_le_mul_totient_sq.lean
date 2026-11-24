-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.le_mul_totient_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:42.525896+00:00
-- url     : https://prove2.me/submissions/a46efaab-bdda-4c41-9ee4-aa8173e68157

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
theorem _root_.solution (n : ℕ) : n ≤ (if Even n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.totient_prime_pow hp hk]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · have he : Even (2 ^ (m + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      rw [if_pos he]
      have h1 : 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
      rw [pow_succ]
      nlinarith
    · have hne : ¬ Even (p ^ (m + 1)) := by
        rw [Nat.not_even_iff_odd]
        exact hodd.pow
      rw [if_neg hne, one_mul]
      have h3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨j, hj⟩
        omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hP : 1 ≤ (q + 1) ^ m := Nat.one_le_pow _ _ (by omega)
      have hq : q + 1 ≤ q ^ 2 := by nlinarith
      calc (q + 1) ^ (m + 1) = (q + 1) ^ m * (q + 1) := pow_succ _ _
        _ ≤ (q + 1) ^ m * q ^ 2 := Nat.mul_le_mul_left _ hq
        _ ≤ ((q + 1) ^ m) ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
        _ = ((q + 1) ^ m * q) ^ 2 := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, mul_pow]
    have hce : (if Even (a * b) then 2 else 1) =
        (if Even a then 2 else 1) * (if Even b then 2 else 1) := by
      by_cases ea : Even a <;> by_cases eb : Even b <;> simp [ea, eb, Nat.even_mul]
      have h2 : 2 ∣ Nat.gcd a b := Nat.dvd_gcd (even_iff_two_dvd.mp ea) (even_iff_two_dvd.mp eb)
      rw [hab.gcd_eq_one] at h2
      norm_num at h2
    calc a * b ≤ ((if Even a then 2 else 1) * a.totient ^ 2) *
          ((if Even b then 2 else 1) * b.totient ^ 2) := Nat.mul_le_mul iha ihb
      _ = _ := by rw [hce]; ring
end Formalism.L2.SG.NGCut.TorsionTotientBound
