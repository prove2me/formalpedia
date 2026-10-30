-- Prove2me | solution 1 for DiazModulus.iteratedDeriv_iteratedFDeriv_line
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:23:42.540838+00:00
-- url     : https://prove2.me/submissions/1da74921-566e-4e87-8a72-60877c6cef06

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Derivatives along a line of an iterated Fréchet derivative

For an entire `f` on `ℂⁿ`, the `q`-th derivative in `z` of `z ↦ D^σ f(z ζ)(v)` is
`D^{σ+q} f(z ζ)(v, ζ, …, ζ)`, for every `z`; the statement is the case `z = 0`.
One derivative: `z ↦ z • ζ` has derivative `ζ`, `D^N f` is differentiable (`f` is `C^∞`) and
evaluation at a fixed tuple is a continuous linear map, so by the chain rule the derivative of
`z ↦ D^N f(z ζ)(w)` is `(D(D^N f)(z ζ) ζ)(w) = D^{N+1} f(z ζ)(ζ, w)`
(`iteratedFDeriv_succ_apply_left`). Induction on `q` (`iteratedDeriv_succ`) then puts the new `ζ`
in front, while the statement has it at the end: `append v (ζ,…,ζ,ζ) = snoc (append v (ζ,…,ζ)) ζ`
(`Fin.append_snoc`), and `snoc w ζ` is `cons ζ w` composed with `finRotate`
(`Fin.snoc_eq_cons_rotate`), so the two values agree by the symmetry of iterated derivatives of a
smooth function (`ContDiffAt.iteratedFDeriv_comp_perm`).
-/

namespace C14_A3
open DiazModulus
open scoped ContDiff

lemma line_deriv {n N : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (ζ : Fin n → ℂ) (w : Fin N → Fin n → ℂ) (z : ℂ) :
    deriv (fun z : ℂ => iteratedFDeriv ℂ N f (z • ζ) w) z =
      iteratedFDeriv ℂ (N + 1) f (z • ζ) (Fin.cons ζ w) := by
  have hΦ : Differentiable ℂ (iteratedFDeriv ℂ N f) :=
    (hf.contDiff (n := ((N + 1 : ℕ) : WithTop ℕ∞))).differentiable_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self N)
  have hline : HasDerivAt (fun y : ℂ => y • ζ) ζ z := by
    simpa using (hasDerivAt_id z).smul_const ζ
  have h1 := (hΦ (z • ζ)).hasFDerivAt.comp_hasDerivAt z hline
  have h2 := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin N => Fin n → ℂ) ℂ w).hasFDerivAt.comp_hasDerivAt
    z h1
  have h3 : HasDerivAt (fun z : ℂ => iteratedFDeriv ℂ N f (z • ζ) w)
      ((fderiv ℂ (iteratedFDeriv ℂ N f) (z • ζ) ζ) w) z := h2
  rw [h3.deriv, iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]

lemma line_all {n σ : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (ζ : Fin n → ℂ) (v : Fin σ → Fin n → ℂ) : ∀ (q : ℕ) (z : ℂ),
    iteratedDeriv q (fun z : ℂ => iteratedFDeriv ℂ σ f (z • ζ) v) z =
      iteratedFDeriv ℂ (σ + q) f (z • ζ) (Fin.append v (fun _ : Fin q => ζ))
  | 0, z => by
    simp only [iteratedDeriv_zero]
    rw [Fin.append_right_nil v _ rfl]
    rfl
  | q + 1, z => by
    rw [iteratedDeriv_succ]
    have : iteratedDeriv q (fun z : ℂ => iteratedFDeriv ℂ σ f (z • ζ) v) =
        fun z => iteratedFDeriv ℂ (σ + q) f (z • ζ) (Fin.append v (fun _ : Fin q => ζ)) :=
      funext (line_all f hf ζ v q)
    rw [this, line_deriv f hf ζ _ z]
    have hc : (fun _ : Fin (q + 1) => ζ) = Fin.snoc (fun _ : Fin q => ζ) ζ := by
      funext i; refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
    rw [hc, Fin.append_snoc, Fin.snoc_eq_cons_rotate]
    exact ((hf.contDiff (n := ω)).contDiffAt.iteratedFDeriv_comp_perm _ _).symm

end C14_A3

open DiazModulus C14_A3 in
theorem solution {n : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (ζ : Fin n → ℂ) (σ q : ℕ) (v : Fin σ → Fin n → ℂ) :
    iteratedDeriv q (fun z : ℂ => iteratedFDeriv ℂ σ f (z • ζ) v) 0 =
      iteratedFDeriv ℂ (σ + q) f 0 (Fin.append v (fun _ : Fin q => ζ)) := by
  simpa using line_all f hf ζ v q 0
