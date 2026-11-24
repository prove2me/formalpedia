-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.teichmuller_unit_all_primes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:58.150676+00:00
-- url     : https://prove2.me/submissions/ce47ab33-a2ff-477e-9ada-a956079d258c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
private theorem witt_frobenius_sq_eq_neg (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (hp2 : p ≠ 2)
    (ε : WittVector p k) (hε : ε ^ (p ^ 2 - 1) = -1) :
    WittVector.frobenius (WittVector.frobenius ε) = -ε := by
  have hp := (Fact.out : p.Prime)
  set N := p ^ 2 - 1 with hN
  have hN1 : N + 1 = p ^ 2 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hNe : Even N := by
    have : Odd (p ^ 2) := hodd.pow
    rw [← hN1] at this
    by_contra h
    rw [Nat.not_even_iff_odd] at h
    exact (Nat.not_even_iff_odd.2 this) (h.add_odd odd_one)
  set a := WittVector.frobenius (WittVector.frobenius ε) with ha
  set b := -ε with hb
  have haN : a ^ N = -1 := by rw [ha, ← map_pow, ← map_pow, hε, map_neg, map_neg, map_one, map_one]
  have hbN : b ^ N = -1 := by rw [hb, hNe.neg_pow, hε]
  have hc := (Commute.all a b).mul_geom_sum₂ N
  rw [haN, hbN, sub_self] at hc
  rcases mul_eq_zero.1 hc with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    let c : WittVector p k →+* k := WittVector.constantCoeff
    have cfrob : ∀ x : WittVector p k, c (WittVector.frobenius x) = c x ^ p := fun x =>
      WittVector.coeff_frobenius_charP p x 0
    have cε : c ε ^ N = -1 := by rw [← map_pow, hε, map_neg, map_one]
    have cab : c a = c b := by
      rw [ha, hb, cfrob, cfrob, ← pow_mul, ← sq, ← hN1, pow_succ, cε, map_neg]; ring
    have cbN : c b ^ N = -1 := by rw [← map_pow, hbN, map_neg, map_one]
    have h2 := congrArg c h1
    rw [map_sum, map_zero] at h2
    have h3 : ∀ i ∈ range N, c (a ^ i * b ^ (N - 1 - i)) = c b ^ (N - 1) := by
      intro i hi
      have := Finset.mem_range.1 hi
      rw [map_mul, map_pow, map_pow, cab, ← pow_add]; congr 1; omega
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have hNk : (N : k) = -1 := by
      have : ((N + 1 : ℕ) : k) = 0 := by rw [hN1]; push_cast; simp
      push_cast at this
      linear_combination this
    have hb0 : c b ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by have := hp.two_le; nlinarith)] at cbN
      exact one_ne_zero (neg_eq_zero.1 cbN.symm)
    rw [hNk] at h2
    exact (mul_ne_zero (neg_ne_zero.2 one_ne_zero) (pow_ne_zero _ hb0)) h2
end Formalism.HermitianLattices.ModelCocycles
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.ModelCocycles
theorem _root_.solution : EpsTeichAll := fun p _ hp2 ε hε => witt_frobenius_sq_eq_neg p _ hp2 ε hε
end Formalism.HermitianLattices.ModelCocycles
