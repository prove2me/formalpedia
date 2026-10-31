-- Prove2me | solution 1 for DiazModulus.le_height_torusVanishing
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:06:25.627243+00:00
-- url     : https://prove2.me/submissions/526902a8-c1a6-4b6d-b1d5-4be6fcbce6ed

import Mathlib
import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_isPrime_iInf_ker_eval_of_analytic

open Complex ComplexConjugate

/-! # The ideal of the torus points has height at least `|A₁|`

A chain of `|A₁| + 1` primes below `I = ⨅_{x, y} ker(eval (x, y, y⁻¹))` in `ℂ[X, Y, Z]`. Number the torus coordinates
`e : A₁ ≃ Fin |A₁|`; the `k`-th member is the ideal of the image of the analytic parametrisation that sets
`(Y_i, Z_i) = (exp u_i, exp(−u_i))` for `e i < k` and leaves `Y_i, Z_i` free otherwise. Each member is prime (the
imported node `isPrime_iInf_ker_eval_of_analytic`), the chain increases, and `Y_iZ_i − 1` with `e i = k` separates
the `k`-th and `(k+1)`-st members (it vanishes on the latter, not at `0`). Iterating
`Ideal.height_add_one_le_of_lt_of_isPrime` gives height `≥ |A₁|` for the last member, which lies below `I` since
every torus point is reached through `exp ∘ log` (`Complex.exp_log`). -/

namespace C13_H1
open DiazModulus

/-- CHAIN. A strict chain of primes `Q 0 < Q 1 < ⋯ < Q n` adds `n` to the height. -/
theorem height_add_le_of_chain {R : Type*} [CommRing R] (n : ℕ) (Q : ℕ → Ideal R)
    (hQ : ∀ i ≤ n, (Q i).IsPrime) (hlt : ∀ i < n, Q i < Q (i + 1)) :
    (Q 0).height + n ≤ (Q n).height := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih (fun i hi => hQ i (by omega)) (fun i hi => hlt i (by omega))
    have := hQ n (by omega)
    have := hQ (n + 1) le_rfl
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (hlt n (by omega))
    calc (Q 0).height + ((n + 1 : ℕ) : ℕ∞) = ((Q 0).height + n) + 1 := by push_cast; ring
      _ ≤ (Q n).height + 1 := by gcongr
      _ ≤ (Q (n + 1)).height := h2

/-- The analytic parametrisation of the `k`-th member of the chain under the torus ideal:
`y_i z_i = 1` is imposed (as `exp(u_i)·exp(−u_i)`) on the coordinates `i` with `e i < k`. -/
noncomputable def chainParam {A₀ A₁ : Type*} (e : A₁ → ℕ) (k : ℕ)
    (p : (A₀ → ℂ) × (A₁ → ℂ) × (A₁ → ℂ)) : A₀ ⊕ (A₁ × Bool) → ℂ :=
  Sum.elim p.1 fun q : A₁ × Bool =>
    if e q.1 < k then (if q.2 then Complex.exp (p.2.1 q.1) else Complex.exp (-p.2.1 q.1))
    else (if q.2 then p.2.1 q.1 else p.2.2 q.1)

theorem chainParam_analytic {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (e : A₁ → ℕ) (k : ℕ) (v : A₀ ⊕ (A₁ × Bool)) :
    AnalyticOnNhd ℂ (fun p : (A₀ → ℂ) × (A₁ → ℂ) × (A₁ → ℂ) => chainParam e k p v) Set.univ := by
  intro p _
  rcases v with h | ⟨i, b⟩
  · simp only [chainParam, Sum.elim_inl]
    exact ((ContinuousLinearMap.proj h : (A₀ → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.fst ℂ (A₀ → ℂ) ((A₁ → ℂ) × (A₁ → ℂ)))).analyticAt p
  · have hu : AnalyticAt ℂ (fun p : (A₀ → ℂ) × (A₁ → ℂ) × (A₁ → ℂ) => p.2.1 i) p :=
      ((ContinuousLinearMap.proj i : (A₁ → ℂ) →L[ℂ] ℂ).comp
        ((ContinuousLinearMap.fst ℂ (A₁ → ℂ) (A₁ → ℂ)).comp
        (ContinuousLinearMap.snd ℂ (A₀ → ℂ) ((A₁ → ℂ) × (A₁ → ℂ))))).analyticAt p
    have hv : AnalyticAt ℂ (fun p : (A₀ → ℂ) × (A₁ → ℂ) × (A₁ → ℂ) => p.2.2 i) p :=
      ((ContinuousLinearMap.proj i : (A₁ → ℂ) →L[ℂ] ℂ).comp
        ((ContinuousLinearMap.snd ℂ (A₁ → ℂ) (A₁ → ℂ)).comp
        (ContinuousLinearMap.snd ℂ (A₀ → ℂ) ((A₁ → ℂ) × (A₁ → ℂ))))).analyticAt p
    simp only [chainParam, Sum.elim_inr]
    split_ifs
    · exact analyticAt_cexp.comp hu
    · exact analyticAt_cexp.comp hu.neg
    · exact hu
    · exact hv

/-- The chain member: polynomials vanishing on the image of `chainParam e k`. -/
noncomputable def chainIdeal {A₀ A₁ : Type*} (e : A₁ → ℕ) (k : ℕ) :
    Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :=
  ⨅ p : (A₀ → ℂ) × (A₁ → ℂ) × (A₁ → ℂ), RingHom.ker (MvPolynomial.eval (chainParam e k p))

theorem chainIdeal_isPrime {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (e : A₁ → ℕ) (k : ℕ) :
    (chainIdeal (A₀ := A₀) e k).IsPrime :=
  DiazModulus.isPrime_iInf_ker_eval_of_analytic _ fun v => chainParam_analytic e k v

theorem chainIdeal_lt {A₀ A₁ : Type*} (e : A₁ → ℕ) (k : ℕ) (i : A₁) (hi : e i = k) :
    chainIdeal (A₀ := A₀) e k < chainIdeal e (k + 1) := by
  classical
  refine lt_of_le_of_ne ?_ ?_
  · intro f hf
    simp only [chainIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hf ⊢
    intro p
    -- the `(k+1)`-point is a `k`-point with the free coordinates at `i` set to `exp(±u_i)`
    let p' : (A₀ → ℂ) × (A₁ → ℂ) × (A₁ → ℂ) :=
      (p.1, fun j => if e j = k then Complex.exp (p.2.1 j) else p.2.1 j,
        fun j => if e j = k then Complex.exp (-p.2.1 j) else p.2.2 j)
    have : chainParam e (k + 1) p = chainParam e k p' := by
      funext v
      rcases v with h | ⟨j, b⟩
      · rfl
      · simp only [chainParam, Sum.elim_inr, p']
        by_cases h1 : e j < k
        · have : e j < k + 1 := by omega
          have : e j ≠ k := by omega
          simp [*]
        · by_cases h2 : e j = k
          · simp [h2]
          · have : ¬ e j < k + 1 := by omega
            simp [*]
    rw [this]; exact hf p'
  · intro hEq
    let F : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ :=
      MvPolynomial.X (Sum.inr (i, true)) * MvPolynomial.X (Sum.inr (i, false)) - 1
    have hin : F ∈ chainIdeal (A₀ := A₀) e (k + 1) := by
      simp only [chainIdeal, Submodule.mem_iInf, RingHom.mem_ker]
      intro p
      simp [F, chainParam, hi, ← Complex.exp_add]
    rw [← hEq] at hin
    simp only [chainIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hin
    have := hin (0, 0, 0)
    simp [F, chainParam, hi] at this
end C13_H1

open DiazModulus C13_H1 in
theorem solution {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] :
    (Fintype.card A₁ : ℕ∞) ≤
      (⨅ (x : A₀ → ℂ) (y : A₁ → ℂˣ),
        RingHom.ker (MvPolynomial.eval (torusPoint x y) :
          MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ →+* ℂ)).height := by
  classical
  let eq := Fintype.equivFin A₁
  let e : A₁ → ℕ := fun i => (eq i : ℕ)
  have hchain := height_add_le_of_chain (Fintype.card A₁) (fun k => chainIdeal (A₀ := A₀) e k)
    (fun k _ => chainIdeal_isPrime e k) (fun k hk => by
      exact chainIdeal_lt e k (eq.symm ⟨k, hk⟩) (by simp [e]))
  refine le_trans (le_trans (le_add_self) hchain) (Ideal.height_mono ?_)
  intro f hf
  simp only [chainIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hf ⊢
  intro x y
  have := hf (x, fun i => Complex.log (y i), 0)
  convert this using 2
  congr 1
  funext v
  rcases v with h | ⟨i, b⟩
  · rfl
  · have hlt : e i < Fintype.card A₁ := (eq i).isLt
    have hy : (y i : ℂ) ≠ 0 := (y i).ne_zero
    cases b <;> simp [chainParam, torusPoint, hlt, Complex.exp_neg, Complex.exp_log hy]
