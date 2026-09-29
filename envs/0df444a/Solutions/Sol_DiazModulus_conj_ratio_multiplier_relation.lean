-- Prove2me | solution 1 for DiazModulus.conj_ratio_multiplier_relation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:34:53.972678+00:00
-- url     : https://prove2.me/submissions/e0e106a9-19dc-47e7-843e-1667b7d49a90

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_six_exponentials

open ComplexConjugate

namespace ConjRatioRel

/-- Complex conjugation as a `ℚ`-algebra map, used to transport algebraicity. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

/-- `ℒ` is stable under conjugation. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact alg_conj hw

end ConjRatioRel

open ConjRatioRel in
/-- Six exponentials at `x = (1, s)`, `y = (ū, w, w')`, with `s = u/ū` and
`w' = conj (s w)`: the six products `ū, w, w', u, s w, s w' = w̄` all lie in `ℒ`.
The independence of `y` is exactly the absence of the relation (multiply by `u`). -/
theorem solution (u w : ℂ) (hre : u.re ≠ 0) (him : u.im ≠ 0)
    (heu : IsAlgebraic ℚ (Complex.exp u)) (hew : IsAlgebraic ℚ (Complex.exp w))
    (hsw : IsAlgebraic ℚ (Complex.exp (u * w / conj u))) :
    ∃ a b c : ℚ, ¬(a = 0 ∧ b = 0 ∧ c = 0) ∧
      (a : ℂ) * (u * conj u) + (b : ℂ) * (u * w) + (c : ℂ) * conj (u * w) = 0 := by
  by_contra hne
  have hu : u ≠ 0 := by
    intro h; apply hre; rw [h, Complex.zero_re]
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu
  have hconj : conj (u * w / conj u) = conj u * conj w / u := by
    rw [map_div₀, map_mul, Complex.conj_conj]
  have huw' : u * conj (u * w / conj u) = conj (u * w) := by
    rw [hconj, map_mul]
    field_simp
  have e10 : u / conj u * conj u = u := div_mul_cancel₀ u hcu
  have e11 : u / conj u * w = u * w / conj u := by ring
  have e12 : u / conj u * conj (u * w / conj u) = conj w := by
    rw [hconj]
    field_simp
  -- `x = (1, u/ū)` is `ℚ`-independent
  have hx : LinearIndependent ℚ ![(1 : ℂ), u / conj u] := by
    rw [LinearIndependent.pair_iff]
    intro a t hat
    simp only [Rat.smul_def, mul_one] at hat
    have h1 : (a : ℂ) * conj u + (t : ℂ) * u = 0 := by
      have e : (t : ℂ) * (u / conj u) * conj u = (t : ℂ) * u := by field_simp
      linear_combination conj u * hat - e
    have hre1 := congrArg Complex.re h1
    have him1 := congrArg Complex.im h1
    simp at hre1 him1
    have h3 : ((a + t : ℚ) : ℝ) * u.re = 0 := by push_cast; linear_combination hre1
    have h4 : ((t - a : ℚ) : ℝ) * u.im = 0 := by push_cast; linear_combination him1
    have h5 : a + t = 0 := by exact_mod_cast (mul_eq_zero.1 h3).resolve_right hre
    have h6 : t - a = 0 := by exact_mod_cast (mul_eq_zero.1 h4).resolve_right him
    constructor <;> linarith
  -- `y = (ū, w, w')` is `ℚ`-independent: a relation, times `u`, is the excluded one
  have hy : LinearIndependent ℚ ![conj u, w, conj (u * w / conj u)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Rat.smul_def] at hg
    have hall : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
      by_contra hnz
      exact hne ⟨g 0, g 1, g 2, hnz, by linear_combination u * hg - (g 2 : ℂ) * huw'⟩
    intro i; fin_cases i
    exacts [hall.1, hall.2.1, hall.2.2]
  have hall : ∀ i j, IsAlgebraic ℚ (Complex.exp
      (![(1 : ℂ), u / conj u] i * ![conj u, w, conj (u * w / conj u)] j)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · change IsAlgebraic ℚ (Complex.exp (1 * conj u)); rw [one_mul]; exact exp_conj_alg heu
    · change IsAlgebraic ℚ (Complex.exp (1 * w)); rw [one_mul]; exact hew
    · change IsAlgebraic ℚ (Complex.exp (1 * conj (u * w / conj u))); rw [one_mul]
      exact exp_conj_alg hsw
    · change IsAlgebraic ℚ (Complex.exp (u / conj u * conj u)); rw [e10]; exact heu
    · change IsAlgebraic ℚ (Complex.exp (u / conj u * w)); rw [e11]; exact hsw
    · change IsAlgebraic ℚ (Complex.exp (u / conj u * conj (u * w / conj u))); rw [e12]
      exact exp_conj_alg hew
  obtain ⟨i, j, hij⟩ := DiazModulus.six_exponentials _ _ hx hy
  exact hij (hall i j)

#print axioms solution
