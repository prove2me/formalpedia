-- Prove2me | solution 1 for DiaconisStroock.VarDist.four_tvDist_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T08:37:24.301038+00:00
-- url     : https://prove2.me/submissions/fd516a37-9166-4318-9540-07acfcfecb11

import Mathlib
import Definitions.Def_mm_mixing
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
-- Extracted from the accepted vardist_root proof; see source-provenance.json.
set_option autoImplicit false
-- BEGIN MODULE VariationChiSquare
section

set_option autoImplicit false

namespace DiaconisStroock.VarDist.Proof

open MarkovMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem tvDist_nonneg (μ π : V → ℝ) : 0 ≤ tvDist μ π := by
  have h := le_ciSup (Set.finite_range (fun A : Finset V =>
    |∑ x ∈ A, μ x - ∑ x ∈ A, π x|)).bddAbove (∅ : Finset V)
  simpa only [tvDist, Finset.sum_empty, sub_self, abs_zero] using h

theorem tvDist_le_half_abs_sum (μ π : V → ℝ) (hμ : IsDist μ) (hπ : IsDist π) :
    tvDist μ π ≤ (∑ x, |μ x - π x|) / 2 := by
  classical
  apply ciSup_le
  intro A
  have hz : ∑ x, (μ x - π x) = 0 := by
    rw [Finset.sum_sub_distrib, hμ.2, hπ.2, sub_self]
  have hsplit := Finset.sum_add_sum_compl A (fun x => μ x - π x)
  rw [hz] at hsplit
  have he : ∑ x ∈ Aᶜ, (μ x - π x) = -(∑ x ∈ A, (μ x - π x)) := by linarith
  have h1 := Finset.abs_sum_le_sum_abs (fun x => μ x - π x) A
  have h2 := Finset.abs_sum_le_sum_abs (fun x => μ x - π x) Aᶜ
  rw [he, abs_neg] at h2
  have hs := Finset.sum_add_sum_compl A (fun x => |μ x - π x|)
  rw [← Finset.sum_sub_distrib]
  linarith

theorem four_tvDist_sq_le_chiSquare (μ π : V → ℝ) (hμ : IsDist μ) (hπ : IsDist π)
    (hpos : ∀ x, 0 < π x) :
    4 * tvDist μ π ^ 2 ≤ ∑ x, (μ x - π x)^2 / π x := by
  have ht := tvDist_le_half_abs_sum μ π hμ hπ
  have ht0 := tvDist_nonneg μ π
  have hsquare := pow_le_pow_left₀ ht0 ht 2
  have hc := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset V)
    (fun x => |μ x - π x|) (fun x _ => hpos x)
  simp only [hπ.2, div_one, sq_abs] at hc
  nlinarith

omit [DecidableEq V] in
theorem chiSquare_eq_second_moment_sub_one (μ π : V → ℝ) (hμ : IsDist μ)
    (hπ : IsDist π) (hpos : ∀ x, 0 < π x) :
    (∑ x, (μ x - π x)^2 / π x) = (∑ x, μ x ^ 2 / π x) - 1 := by
  have he (x : V) : (μ x - π x)^2 / π x = μ x ^ 2 / π x - 2 * μ x + π x := by
    field_simp [(hpos x).ne']
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hμ.2, hπ.2]
  ring

end DiaconisStroock.VarDist.Proof

end
-- END MODULE VariationChiSquare

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
-- Proof bodies extracted from the accepted vardist_root DiagonalVariation module.
set_option autoImplicit false
namespace DiaconisStroock.VarDist.Proof
open MarkovMixing
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem rowDist_isDist (P : Matrix V V ℝ) (hP : IsStochastic P) (n : ℕ) (x : V) :
    IsDist (rowDist P n x) :=
  ⟨(stochastic_pow P hP n).1 x, (stochastic_pow P hP n).2 x⟩

theorem four_tvDist_sq_le_diagonal (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (x : V) (n : ℕ) :
    4 * tvDist (rowDist P n x) π ^ 2 ≤ (P^(2*n)) x x / π x - 1 := by
  have hpos := stationary_positive P hP hirr π hπ
  have hμ := rowDist_isDist P hP n x
  have ht := four_tvDist_sq_le_chiSquare (rowDist P n x) π hμ hπ.1 hpos
  rw [chiSquare_eq_second_moment_sub_one (rowDist P n x) π hμ hπ.1 hpos] at ht
  change 4 * tvDist (rowDist P n x) π ^ 2 ≤ (∑ y, (P^n) x y ^ 2 / π y) - 1 at ht
  rwa [sum_square_div_eq_diagonal P π hpos hrev n x] at ht

end DiaconisStroock.VarDist.Proof

-- SPDX-License-Identifier: Apache-2.0
-- Reused accepted proof modules are credited in source-provenance.json.
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.VarDist


/-- The Cauchy–Schwarz step in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds
for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`4‖Pⁿ(x, ·) − π‖²_Var ≤ (1/π(x)) P^{2n}(x, x) − 1` for every state `x` and every `n`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), 4 * tvDist (rowDist P n x) π ^ 2 ≤ (P ^ (2 * n)) x x / π x - 1 := by
  intro x n
  exact DiaconisStroock.VarDist.Proof.four_tvDist_sq_le_diagonal P hP hirr π hπ hrev x n



#print axioms solution

open MarkovMixing
open scoped BigOperators
namespace DiaconisStroock.VarDist

/-- The Cauchy–Schwarz step in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds
for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`4‖Pⁿ(x, ·) − π‖²_Var ≤ (1/π(x)) P^{2n}(x, x) − 1` for every state `x` and every `n`. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), 4 * tvDist (rowDist P n x) π ^ 2 ≤ (P ^ (2 * n)) x x / π x - 1 := by
  exact solution P hP hirr π hπ hrev

end DiaconisStroock.VarDist

#print axioms solution
