-- Prove2me | solution 1 for DeciSigma1.Words.PeriodicOn.eq_of_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:35.492609+00:00
-- url     : https://prove2.me/submissions/9372fcd0-b4a1-4295-8e1b-d4b402740f0f

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_le_add

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
open DeciSigma1.Words.PeriodicOn
variable {w : List α} {d s e : ℕ}
namespace DeciSigma1.Words.PeriodicOn
theorem _root_.solution (h : PeriodicOn w d s e) {p q : ℕ} (hp : s ≤ p) (hq : s ≤ q) (hpe : p < e)
    (hqe : q < e) (hpq : p % d = q % d) : w[p]? = w[q]? := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.mod_zero] at hpq; rw [hpq]
  rcases le_total p q with hle | hle
  · obtain ⟨j, hj⟩ : d ∣ q - p := (Nat.modEq_iff_dvd' hle).mp hpq
    have : q = p + j * d := by rw [mul_comm]; omega
    rw [this]; exact h.eq_of_le_add hp j (by omega)
  · obtain ⟨j, hj⟩ : d ∣ p - q := (Nat.modEq_iff_dvd' hle).mp hpq.symm
    have : p = q + j * d := by rw [mul_comm]; omega
    rw [this]; exact (h.eq_of_le_add hq j (by omega)).symm
end DeciSigma1.Words.PeriodicOn
