-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.sum_vonMangoldt_not_coprime_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:15.340282+00:00
-- url     : https://prove2.me/submissions/4642fa65-cbd2-4ddc-a553-df61f6415f2b

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) (hq : q ≠ 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, Λ n * (if n.Coprime q then 0 else 1) ≤ (Nat.log 2 N : ℝ) * Real.log q := by
  set K := Nat.log 2 N
  set g : ℕ → ℝ := fun n => Λ n * (if n.Coprime q then 0 else 1) with hg
  have hgle : ∀ n, g n ≤ Λ n := fun n => by
    simp only [hg]; split_ifs <;> simp [vonMangoldt_nonneg]
  have hsub : (Icc 1 N).filter (fun n => g n ≠ 0) ⊆ (q ^ K).divisors := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hN⟩, hgn⟩ := hn
    have hΛ : Λ n ≠ 0 := by intro h; apply hgn; simp [hg, h]
    have hnc : ¬ n.Coprime q := by intro h; apply hgn; simp [hg, h]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hpq : p ∣ q := by
      by_contra hc
      exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hc))
    have hkK : k ≤ K := by
      apply Nat.le_log_of_pow_le one_lt_two
      exact le_trans (Nat.pow_le_pow_left hp.two_le k) hN
    rw [Nat.mem_divisors]
    exact ⟨(pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK), pow_ne_zero _ hq⟩
  calc ∑ n ∈ Icc 1 N, g n = ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), g n :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => g n ≠ 0), Λ n := Finset.sum_le_sum fun n _ => hgle n
    _ ≤ ∑ n ∈ (q ^ K).divisors, Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = (K : ℝ) * Real.log q := by rw [vonMangoldt_sum, Nat.cast_pow, Real.log_pow]
end Formalism.ZeroFreeDirichlet
