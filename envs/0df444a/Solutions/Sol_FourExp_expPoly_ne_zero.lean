-- Prove2me | solution 1 for FourExp.expPoly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-14T20:21:25.631162+00:00
-- url     : https://prove2.me/submissions/143df69b-febd-4e1e-a022-eaee5208a3f1

import Mathlib

open Polynomial Finset

namespace FourExpE0

/-- The size of a polynomial for the induction: `0` for the zero polynomial, `deg + 1` otherwise. -/
noncomputable def meas (p : ℂ[X]) : ℕ := if p = 0 then 0 else p.natDegree + 1

/-- For `c ≠ 0`, the operator `p ↦ p' + c p` has trivial kernel. -/
theorem eq_zero_of_derivative_add {p : ℂ[X]} {c : ℂ} (hc : c ≠ 0)
    (h : derivative p + C c * p = 0) : p = 0 := by
  by_contra hp
  have hcoeff := congrArg (fun r => r.coeff p.natDegree) h
  simp only [coeff_add, coeff_derivative, coeff_C_mul, coeff_zero] at hcoeff
  rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul, zero_add] at hcoeff
  exact mul_ne_zero hc (leadingCoeff_ne_zero.mpr hp) hcoeff

/-- The operator `p ↦ p' + c p` does not increase the size. -/
theorem meas_derivative_add_le (p : ℂ[X]) (c : ℂ) : meas (derivative p + C c * p) ≤ meas p := by
  by_cases hp : p = 0
  · simp [meas, hp]
  · unfold meas
    rw [if_neg hp]
    split_ifs with hq
    · exact Nat.zero_le _
    · have h1 : (derivative p).natDegree ≤ p.natDegree :=
        (natDegree_derivative_le p).trans (Nat.sub_le _ _)
      have h2 : (C c * p).natDegree ≤ p.natDegree := natDegree_C_mul_le c p
      have h3 : (derivative p + C c * p).natDegree ≤ p.natDegree :=
        (natDegree_add_le _ _).trans (max_le h1 h2)
      omega

/-- Differentiation strictly decreases the size of a non-zero polynomial. -/
theorem meas_derivative_lt {p : ℂ[X]} (hp : p ≠ 0) : meas (derivative p) < meas p := by
  unfold meas
  rw [if_neg hp]
  split_ifs with hq
  · exact Nat.succ_pos _
  · have hdeg : p.natDegree ≠ 0 := by
      intro h0
      exact hq (derivative_of_natDegree_zero h0)
    have := natDegree_derivative_lt hdeg
    omega

/-- Polynomial form: `∑ Pⱼ(z) e^{ωⱼ z} ≡ 0` with distinct `ωⱼ` forces every `Pⱼ = 0`. -/
theorem poly_form (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∀ n : ℕ, ∀ ω : ι → ℂ, Function.Injective ω → ∀ P : ι → ℂ[X],
      ∑ j, meas (P j) = n →
      (∀ z : ℂ, ∑ j, (P j).eval z * Complex.exp (ω j * z) = 0) → ∀ j, P j = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ω hω P hM hvan
  by_contra hne
  push_neg at hne
  obtain ⟨j₀, hj₀⟩ := hne
  set c : ι → ℂ := fun j => ω j - ω j₀ with hc
  set Q : ι → ℂ[X] := fun j => derivative (P j) + C (c j) * P j with hQ
  -- `e^{-ω_{j₀} z} f(z) = ∑ Pⱼ(z) e^{cⱼ z}` vanishes, hence so does its derivative
  have hg : ∀ w : ℂ, ∑ j, (P j).eval w * Complex.exp (c j * w) = 0 := by
    intro w
    have : ∑ j, (P j).eval w * Complex.exp (c j * w)
        = Complex.exp (-(ω j₀ * w)) * ∑ j, (P j).eval w * Complex.exp (ω j * w) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hc]
      simp only
      rw [show (ω j - ω j₀) * w = -(ω j₀ * w) + ω j * w by ring, Complex.exp_add]
      ring
    rw [this, hvan w, mul_zero]
  have hvan' : ∀ z : ℂ, ∑ j, (Q j).eval z * Complex.exp (c j * z) = 0 := by
    intro z
    have hd : HasDerivAt (fun w => ∑ j, (P j).eval w * Complex.exp (c j * w))
        (∑ j, (Q j).eval z * Complex.exp (c j * z)) z := by
      have hterm : ∀ j ∈ (Finset.univ : Finset ι),
          HasDerivAt (fun w => (P j).eval w * Complex.exp (c j * w))
            ((Q j).eval z * Complex.exp (c j * z)) z := by
        intro j _
        have h1 := (P j).hasDerivAt z
        have h2 : HasDerivAt (fun w => Complex.exp (c j * w)) (Complex.exp (c j * z) * c j) z := by
          have := ((hasDerivAt_id z).const_mul (c j)).cexp
          simpa using this
        have h3 := h1.mul h2
        have hval : eval z (Q j) * Complex.exp (c j * z)
            = eval z (derivative (P j)) * Complex.exp (c j * z)
              + eval z (P j) * (Complex.exp (c j * z) * c j) := by
          rw [show eval z (Q j) = eval z (derivative (P j)) + c j * eval z (P j) by
            simp [hQ]]
          ring
        rw [hval]
        exact h3
      have := HasDerivAt.sum hterm
      rw [Finset.sum_fn] at this
      exact this
    have h0 : HasDerivAt (fun w => ∑ j, (P j).eval w * Complex.exp (c j * w)) 0 z := by
      have : (fun w => ∑ j, (P j).eval w * Complex.exp (c j * w)) = fun _ => 0 := funext hg
      rw [this]
      exact hasDerivAt_const z 0
    exact hd.unique h0
  have hcinj : Function.Injective c := by
    intro a b h
    apply hω
    simpa [hc] using h
  -- the size drops
  have hle : ∀ j ∈ (Finset.univ : Finset ι), meas (Q j) ≤ meas (P j) :=
    fun j _ => meas_derivative_add_le (P j) (c j)
  have hlt : meas (Q j₀) < meas (P j₀) := by
    have : Q j₀ = derivative (P j₀) := by simp [hQ, hc]
    rw [this]
    exact meas_derivative_lt hj₀
  have hM' : ∑ j, meas (Q j) < n := by
    rw [← hM]
    exact Finset.sum_lt_sum hle ⟨j₀, Finset.mem_univ _, hlt⟩
  have hQ0 := ih _ hM' c hcinj Q rfl hvan'
  have hPj : ∀ j, j ≠ j₀ → P j = 0 := by
    intro j hj
    have hcj : c j ≠ 0 := sub_ne_zero.mpr (hω.ne hj)
    exact eq_zero_of_derivative_add hcj (by simpa [hQ] using hQ0 j)
  have hroot : ∀ z : ℂ, (P j₀).eval z = 0 := by
    intro z
    have h := hvan z
    rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [hPj j hj]; simp) (by simp)] at h
    exact (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)
  exact hj₀ (Polynomial.funext (fun z => by simpa using hroot z))

end FourExpE0

theorem solution
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0) :
    ∃ w : ℂ, ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, i, hji⟩ := hb
  let P : Fin l → ℂ[X] := fun j => ∑ i : Fin (q j), C (b j i) * X ^ (i : ℕ)
  have hvan : ∀ z : ℂ, ∑ j, (P j).eval z * Complex.exp (ω j * z) = 0 := by
    intro z
    rw [← hcon z]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [P, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, Finset.sum_mul]
  have hP := FourExpE0.poly_form (Fin l) _ ω hω P rfl hvan j
  have hc := congrArg (fun p => p.coeff (i : ℕ)) hP
  simp only [P, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun k _ hk => if_neg (fun h => hk (Fin.ext h).symm)) (by simp)] at hc
  simp only [if_true] at hc
  exact hji hc
