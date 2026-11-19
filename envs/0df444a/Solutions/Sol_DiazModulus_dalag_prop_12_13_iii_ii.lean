-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_13_iii_ii
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:22:35.724665+00:00
-- url     : https://prove2.me/submissions/1e0b57e3-bb8c-4f18-a1a0-8390cc85d34d

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # DALAG Prop. 12.13, (iii) ⇒ (ii)

Take `x₀ = 1`. Let `p ∈ k[X₁, …, X_n]` vanish at `x` and suppose `p ≠ 0`. Homogenise it: with `D` the total degree
of `p` and `p_d` its homogeneous component of degree `d`, put `H = Σ_{d ≤ D} Y₀^{D-d} p_d(Y₁, …, Y_n)`, a
polynomial in `Y₀, …, Y_n`, homogeneous of degree `D`. For any tuple `z` in any `k`-algebra, `H(1, z) = Σ_d p_d(z) =
p(z)`. At the generic point `z = (X₁, …, X_n)` this gives `H(1, X) = p ≠ 0`, so `H ≠ 0`. The tuple
`(1, x₁, …, x_n)` lies in `E` (as `1 ∈ E`) and is `k`-linearly independent, so (iii) gives `H(1, x) ≠ 0`; but
`H(1, x) = p(x) = 0`, a contradiction. Hence `x` is algebraically independent over `k`. -/

namespace RC8B_P1213iii
open DiazModulus

/-- The homogenisation of `p` in degree `D`, the new variable in position `0`. -/
noncomputable def homog {k : Type*} [CommRing k] {n : ℕ} (p : MvPolynomial (Fin n) k) (D : ℕ) :
    MvPolynomial (Fin (n + 1)) k :=
  ∑ d ∈ Finset.range (D + 1),
    MvPolynomial.X 0 ^ (D - d) * MvPolynomial.rename Fin.succ (MvPolynomial.homogeneousComponent d p)

theorem homog_isHomogeneous {k : Type*} [CommRing k] {n : ℕ} (p : MvPolynomial (Fin n) k) (D : ℕ) :
    (homog p D).IsHomogeneous D := by
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  have hdD : d ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  have h := (MvPolynomial.isHomogeneous_X_pow (R := k) (0 : Fin (n + 1)) (D - d)).mul
    ((MvPolynomial.homogeneousComponent_isHomogeneous d p).rename_isHomogeneous (f := Fin.succ))
  rwa [Nat.sub_add_cancel hdD] at h

/-- `H(1, z) = p(z)`, in any `k`-algebra. -/
theorem homog_eval {k S : Type*} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (z : Fin n → S) :
    MvPolynomial.aeval (Fin.cons 1 z : Fin (n + 1) → S) (homog p p.totalDegree) =
      MvPolynomial.aeval z p := by
  have hz : (Fin.cons 1 z : Fin (n + 1) → S) ∘ Fin.succ = z := funext fun i => Fin.cons_succ _ _ _
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent p]
  simp only [homog, map_sum, map_mul, map_pow, MvPolynomial.aeval_X, Fin.cons_zero, one_pow, one_mul,
    MvPolynomial.aeval_rename, hz]

end RC8B_P1213iii

open DiazModulus RC8B_P1213iii in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (h1 : (1 : K) ∈ E)
    (hiii : ∀ (n D : ℕ) (x : Fin (n + 1) → K), LinearIndependent k x → (∀ i, x i ∈ E) →
      ∀ P : MvPolynomial (Fin (n + 1)) k, P.IsHomogeneous D → P ≠ 0 → MvPolynomial.aeval x P ≠ 0)
    {n : ℕ} (x : Fin n → K) (hxE : ∀ i, x i ∈ E)
    (hx : LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K)) :
    AlgebraicIndependent k x := by
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  have hH0 : homog p p.totalDegree ≠ 0 := by
    intro h
    apply hp0
    have := homog_eval p (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k)
    rw [h, map_zero, MvPolynomial.aeval_X_left_apply] at this
    exact this.symm
  have hE : ∀ i, (Fin.cons (1 : K) x : Fin (n + 1) → K) i ∈ E := fun i =>
    Fin.cases (by simpa using h1) (fun j => by simpa using hxE j) i
  exact hiii n p.totalDegree _ hx hE _ (homog_isHomogeneous p _) hH0 (by rw [homog_eval]; exact hp)
