-- Prove2me | solution 1 for BoxLocalization.exhaustion_by_count
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:31:38.335208+00:00
-- url     : https://prove2.me/submissions/fb9c6101-211a-4c70-8808-f665bcb61c74

import Definitions.Def_ArdaRH65K_XiLineZeros
import Mathlib

/- Task 6 (Stage 3): RH-IN-A-BOX LOCALIZATION CAPSTONE.

   Box `B = [2/5, 3/5] x [10, 35]`.  This file composes the three kernel results of the project into
   the crowning statement: EVERY nontrivial zero of `riemannZeta` in `B` lies on the critical line
   `Re = 1/2` (and is simple).  This is a Turing-style VERIFICATION OF RH INSIDE THIS BOX.  It is NOT
   a proof of the Riemann Hypothesis.  `conjecture1_proved = False`.

   The pieces composed:

   1. TOTAL COUNT = 5 (kernel argument principle):
      `BoxArgPrincipleZeta.box_arg_principle_zeta'` concludes `∃ s d, Σ_{ρ∈s} (d ρ) = N`, where `s`
      is the ACTUAL zeta divisor support on the ball `U = ball cB 13 ⊇ B` and `d` its multiplicity
      (`MeromorphicOn.divisor riemannZeta U`), GIVEN the honest Arb bundle `hArb` at `N = 5`.  The
      winding integer `N = 5`, edge non-vanishing, strict interiority, and the value enclosures are
      the documented NON-KERNEL Arb inputs (same trust boundary as Stage 1's enclosures).

   2. ON-LINE LOWER BOUND >= 5 (kernel, Stage 1):
      `XiLineZeros.lambda_five_zeros_10_35` yields 5 DISTINCT `completedRiemannZeta` zeros on the line
      `Re = 1/2` with imaginary parts in `(10, 35)` (from Arb-certified sign changes).

   3. LAMBDA <-> ZETA BRIDGE (kernel, this file):
      In `B` (`Re > 0`, so `s ≠ 0`), `riemannZeta s = completedRiemannZeta s / Gammaℝ s` with
      `Gammaℝ s ≠ 0`; hence `riemannZeta s = 0 ↔ completedRiemannZeta s = 0`.  The 5 on-line
      `completedRiemannZeta`-zeros ARE 5 distinct on-line `riemannZeta`-zeros in `B`.

   COUNTING ARGUMENT (kernel, this file): the divisor is nonnegative (zeta is analytic on `U`, no
   poles), so `d ρ ≥ 1` at every zero.  The 5 distinct on-line zeros lie in the support `s`, each
   with `d ≥ 1`, summing to `≥ 5`.  Since the TOTAL is exactly `5`, they EXHAUST the divisor: the
   support equals those 5 points and each multiplicity is exactly 1.  Therefore every zeta-zero in
   `B` is one of the 5 on-line zeros -- so it lies on `Re = 1/2` and is simple.

   conjecture1_proved = False. -/




open Complex Real

section
namespace BoxLocalization
end BoxLocalization
open BoxLocalization

/-! ## Part A: the pure combinatorial localization lemma (kernel).

If a finite multiset-with-multiplicity `d ≥ 1` on a support `s` sums to `n`, and we already exhibit
`n` DISTINCT elements of `s`, then `s` is EXACTLY those `n` elements and every multiplicity is `1`.
This is the load-bearing counting step; it is fully general and kernel-proven. -/


theorem solution {s T : Finset ℂ} {d : ℂ → ℤ} {n : ℕ}
    (hTsub : T ⊆ s) (hTcard : T.card = n)
    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)
    (hsum : (∑ ρ ∈ s, d ρ) = (n : ℤ)) :
    s = T ∧ ∀ ρ ∈ s, d ρ = 1 := by
  -- Split the sum over `s` into `T` and `s \ T`.
  have hsplit : (∑ ρ ∈ s, d ρ) = (∑ ρ ∈ T, d ρ) + (∑ ρ ∈ s \ T, d ρ) := by
    rw [← Finset.sum_sdiff hTsub, add_comm]
  -- Lower bound on the `T`-sum: each term `≥ 1`, so `∑_T d ≥ T.card = n`.
  have hTlb : (n : ℤ) ≤ ∑ ρ ∈ T, d ρ := by
    calc (n : ℤ) = ∑ _ρ ∈ T, (1 : ℤ) := by rw [Finset.sum_const, hTcard, nsmul_eq_mul, mul_one]
      _ ≤ ∑ ρ ∈ T, d ρ := Finset.sum_le_sum (fun ρ hρ => hd1 ρ (hTsub hρ))
  -- Lower bound on the `s \ T` sum: each term `≥ 1 ≥ 0`, so `∑_{s\T} d ≥ (s\T).card`.
  have hSlb : ((s \ T).card : ℤ) ≤ ∑ ρ ∈ s \ T, d ρ := by
    calc ((s \ T).card : ℤ) = ∑ _ρ ∈ s \ T, (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ ρ ∈ s \ T, d ρ := Finset.sum_le_sum (fun ρ hρ => hd1 ρ (Finset.mem_sdiff.mp hρ).1)
  -- Combine: `n = ∑_s d = ∑_T d + ∑_{s\T} d ≥ n + (s\T).card`, forcing `(s\T).card = 0`.
  have hcard0 : (s \ T).card = 0 := by
    have : (n : ℤ) + ((s \ T).card : ℤ) ≤ (n : ℤ) := by
      calc (n : ℤ) + ((s \ T).card : ℤ)
          ≤ (∑ ρ ∈ T, d ρ) + (∑ ρ ∈ s \ T, d ρ) := add_le_add hTlb hSlb
        _ = (∑ ρ ∈ s, d ρ) := hsplit.symm
        _ = (n : ℤ) := hsum
    have hle : ((s \ T).card : ℤ) ≤ 0 := by linarith
    exact_mod_cast le_antisymm hle (by positivity)
  -- `(s \ T).card = 0` means `s \ T = ∅`, i.e. `s ⊆ T`; with `T ⊆ s` this gives `s = T`.
  have hsubT : s ⊆ T := by
    have : s \ T = ∅ := Finset.card_eq_zero.mp hcard0
    intro x hx
    by_contra hxT
    exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxT⟩) (by rw [this]; exact Finset.notMem_empty x)
  have hsT : s = T := le_antisymm hsubT hTsub
  refine ⟨hsT, ?_⟩
  -- Multiplicity one: with `s = T` and `∑_T d = T.card`, each `d ρ ≥ 1` forces `d ρ = 1`.
  have hsumT : (∑ ρ ∈ T, d ρ) = (T.card : ℤ) := by
    have h1 : (∑ ρ ∈ T, d ρ) = (n : ℤ) := by rw [← hsT]; exact hsum
    rw [h1, hTcard]
  intro ρ hρ
  rw [hsT] at hρ
  -- If some `d ρ > 1` the total would exceed `T.card`.
  by_contra hne
  have hgt : (1 : ℤ) < d ρ := lt_of_le_of_ne (hd1 ρ (hTsub hρ)) (Ne.symm hne)
  have hstrict : (T.card : ℤ) < ∑ ρ' ∈ T, d ρ' := by
    calc (T.card : ℤ) = ∑ _ρ' ∈ T, (1 : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ < ∑ ρ' ∈ T, d ρ' :=
          Finset.sum_lt_sum (fun ρ' hρ' => hd1 ρ' (hTsub hρ')) ⟨ρ, hρ, hgt⟩
  rw [hsumT] at hstrict
  exact lt_irrefl _ hstrict
