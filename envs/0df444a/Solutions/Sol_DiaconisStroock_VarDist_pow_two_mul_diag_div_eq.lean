-- Prove2me | solution 1 for DiaconisStroock.VarDist.pow_two_mul_diag_div_eq
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T08:37:26.854984+00:00
-- url     : https://prove2.me/submissions/c67291de-0c6d-4850-8cde-aae691abfa0d

import Mathlib
import Definitions.Def_mm_basic

-- SPDX-License-Identifier: Apache-2.0
-- Extracted from the accepted vardist_root proof; see source-provenance.json.
set_option autoImplicit false
-- BEGIN MODULE MarkovPowers
section

set_option autoImplicit false

namespace DiaconisStroock.VarDist.Proof

open MarkovMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem stochastic_pow (P : Matrix V V ℝ) (hP : IsStochastic P) (n : ℕ) :
    IsStochastic (P^n) := by
  induction n with
  | zero =>
    constructor
    · intro x y; by_cases h : x = y <;> simp [h]
    · intro x; simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ]
    constructor
    · intro x y
      exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih.1 x z) (hP.1 z y))
    · intro x
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hP.2, mul_one]
      exact ih.2 x

theorem stationary_pow (P : Matrix V V ℝ) (π : V → ℝ)
    (hπ : IsStationary P π) (n : ℕ) : Matrix.vecMul π (P^n) = π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

theorem stationary_positive (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ x, 0 < π x := by
  intro x
  have he : ∃ z, 0 < π z := by
    by_contra hh
    push Not at hh
    have hz : ∀ z, π z = 0 := fun z => le_antisymm (hh z) (hπ.1.1 z)
    have h := hπ.1.2
    simp only [hz, Finset.sum_const_zero] at h
    norm_num at h
  obtain ⟨z, hz⟩ := he
  obtain ⟨n, hn⟩ := hirr z x
  have hb : π z * (P^n) z x ≤ ∑ y, π y * (P^n) y x :=
    Finset.single_le_sum (fun y _ => mul_nonneg (hπ.1.1 y) ((stochastic_pow P hP n).1 y x))
      (Finset.mem_univ z)
  have heq := congrFun (stationary_pow P π hπ n) x
  change (∑ y, π y * (P^n) y x) = π x at heq
  exact (mul_pos hz hn).trans_le (hb.trans_eq heq)

theorem detailedBalance_pow (P : Matrix V V ℝ) (π : V → ℝ)
    (hdb : DetailedBalance P π) (n : ℕ) : DetailedBalance (P^n) π := by
  induction n with
  | zero =>
    intro x y
    by_cases h : x = y
    · subst y; rfl
    · simp [h, Ne.symm h]
  | succ n ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    have ht (z : V) : π x * ((P^n) x z * P z y) = (P^n) z x * (π y * P y z) := by
      calc _ = (π x * (P^n) x z) * P z y := by ring
        _ = (π z * (P^n) z x) * P z y := by rw [ih x z]
        _ = (P^n) z x * (π z * P z y) := by ring
        _ = _ := by rw [hdb z y]
    simp_rw [ht]
    have hp : P^n * P = P * P^n := (Commute.self_pow P n).eq.symm
    rw [hp, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => by ring)

end DiaconisStroock.VarDist.Proof

end
-- END MODULE MarkovPowers

-- SPDX-License-Identifier: Apache-2.0
-- Proof bodies extracted from the accepted vardist_root DiagonalVariation module.
set_option autoImplicit false
namespace DiaconisStroock.VarDist.Proof
open MarkovMixing
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem sum_square_div_eq_diagonal (P : Matrix V V ℝ) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (hrev : DetailedBalance P π) (n : ℕ) (x : V) :
    (∑ y, (P^n) x y ^ 2 / π y) = (P^(2*n)) x x / π x := by
  rw [two_mul, pow_add, Matrix.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  have h := detailedBalance_pow P π hrev n x y
  field_simp [(hpos x).ne', (hpos y).ne']
  linear_combination (P^n) x y * h

end DiaconisStroock.VarDist.Proof

-- SPDX-License-Identifier: Apache-2.0
-- Reused accepted proof modules are credited in source-provenance.json.
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.VarDist


/-- The reversibility identity in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds
for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`(1/π(x)) P^{2n}(x, x) = ∑_y (Pⁿ(x, y))² / π(y)` for every state `x` and every `n`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), (P ^ (2 * n)) x x / π x = ∑ y, ((P ^ n) x y) ^ 2 / π y := by
  intro x n
  have hpos := DiaconisStroock.VarDist.Proof.stationary_positive P hP hirr π hπ
  exact (DiaconisStroock.VarDist.Proof.sum_square_div_eq_diagonal P π hpos hrev n x).symm



#print axioms solution

open MarkovMixing
open scoped BigOperators
namespace DiaconisStroock.VarDist

/-- The reversibility identity in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds
for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`(1/π(x)) P^{2n}(x, x) = ∑_y (Pⁿ(x, y))² / π(y)` for every state `x` and every `n`. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), (P ^ (2 * n)) x x / π x = ∑ y, ((P ^ n) x y) ^ 2 / π y := by
  exact solution P hP hirr π hπ hrev

end DiaconisStroock.VarDist

#print axioms solution
