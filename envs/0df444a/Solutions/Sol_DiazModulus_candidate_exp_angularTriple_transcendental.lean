-- Prove2me | solution 1 for DiazModulus.candidate_exp_angularTriple_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T17:59:08.587828+00:00
-- url     : https://prove2.me/submissions/212c5c15-a013-48a5-a383-d6ed2a7368d2

import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_six_exponentials

open Complex ComplexConjugate

/-!
# `exp (u² / conj u)` is transcendental at a candidate

Let `u` be a candidate: `u ≠ 0`, `|u|` algebraic, `exp u` algebraic. Write `c = u * conj u`
(non-zero and algebraic, because `c = |u|²`) and `t = u² / c`.

Feed the six exponentials theorem the two families `x = (u, conj u)` and `y = (1, t, t⁻¹)`.
Their product matrix is

```
[ u        u³/c     conj u       ]
[ conj u   u        (conj u)²/u  ]
```

using `u * t⁻¹ = c / u = conj u` and `conj u * t = u`; and `u³/c = u²/conj u` is the exponent in
the statement, while `(conj u)²/u` is its complex conjugate. Four of the six entries are `u` or
`conj u`, whose exponentials are algebraic by the candidate hypothesis together with the fact
that conjugation preserves algebraicity. So if `exp (u²/conj u)` were algebraic, its conjugate
would be too and all six exponentials would be algebraic — which the six exponentials theorem
forbids, once the two families are `ℚ`-linearly independent.

Both independence claims come from Hermite–Lindemann, which makes `u` transcendental: a rational
relation between `u` and `conj u` makes `u/conj u = u²/c` rational and hence `u` algebraic, and a
rational relation among `1, t, t⁻¹`, multiplied by `t`, is a non-zero rational polynomial of
degree at most `2` vanishing at `t`, whereas `t` is transcendental for the same reason.

## Attribution

This is **not new**. Diaz proves a stronger statement in *Produits et quotients de combinaisons
linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels*,
J. Théor. Nombres Bordeaux **19** (2007), 373–391, **théorème 7(1)**, p. 390: for `u, v ∈ ℂ` with
`(1, u, conj u)` and `(v, conj v)` both `Q̄`-free, `{v, v·u, v·conj u} ⊄ ℒ̃`. Taking `v := u` and
his `u := u / conj u` gives `{u, u²/conj u, conj u} ⊄ ℒ̃`, and `ℒ̃ ⊋ ℒ`. His proof uses the
**strong** six exponentials theorem.

The only thing observed here is that the **ordinary** six exponentials theorem already suffices
for the weaker conclusion about `ℒ` — an implementation remark, not a transcendence result.
-/

/-- Algebraicity over `ℚ` survives complex conjugation: a rational polynomial killing `z`
has coefficients fixed by `conj`, so it kills `conj z` too. -/
private theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) :
    IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hpz⟩ := h
  refine ⟨p, hp0, ?_⟩
  have hc := congrArg (starRingEnd ℂ) hpz
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, map_sum, Polynomial.sum]
    using hc

/-- The whole argument, with the two published nodes it consumes — Hermite–Lindemann and the
six exponentials theorem — taken as explicit hypotheses, so that the mathematical content can be
checked to use no axioms beyond the ambient three. -/
private theorem core (hHL : DiazModulus.HermiteLindemann)
    (hSix : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
      ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)))
    {u : ℂ} (h : DiazModulus.IsCandidate u) :
    Transcendental ℚ (Complex.exp (u ^ 2 / conj u)) := by
  obtain ⟨hu0, hmod, hexp⟩ := h
  have hcu0 : conj u ≠ 0 := by simpa using hu0
  -- `c := u * conj u = ‖u‖ ^ 2` is a non-zero algebraic number
  have hcc : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hcQ : u * conj u ∈ DiazModulus.Qbar := by
    rw [hcc]; exact pow_mem (DiazModulus.mem_Qbar_iff.mpr hmod) 2
  have hc0 : u * conj u ≠ 0 := mul_ne_zero hu0 hcu0
  -- Hermite–Lindemann: `u` itself is transcendental
  have hutr : ¬ IsAlgebraic ℚ u := fun ha => hHL u hu0 ha hexp
  set t : ℂ := u ^ 2 / (u * conj u) with ht_def
  have ht0 : t ≠ 0 := by
    rw [ht_def]; exact div_ne_zero (pow_ne_zero 2 hu0) hc0
  -- and so is `t = u ^ 2 / c`: otherwise `u ^ 2 = c * t` would be algebraic, hence `u`
  have httr : ¬ IsAlgebraic ℚ t := by
    intro hta
    refine hutr (IsAlgebraic.of_pow two_pos ?_)
    have hu2 : u ^ 2 = (u * conj u) * t := by rw [ht_def]; field_simp
    rw [hu2]
    exact DiazModulus.mem_Qbar_iff.mp
      (mul_mem hcQ (DiazModulus.mem_Qbar_iff.mpr hta))
  -- the first family: `(u, conj u)`
  have hxli : LinearIndependent ℚ ![u, conj u] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    simp only [Rat.smul_def] at hab
    by_cases ha : a = 0
    · subst ha
      have hb : (b : ℂ) = 0 := by
        simp only [Rat.cast_zero, zero_mul, zero_add] at hab
        rcases mul_eq_zero.mp hab with h' | h'
        · exact h'
        · exact absurd h' hcu0
      exact ⟨rfl, by exact_mod_cast hb⟩
    · exfalso
      apply hutr
      have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      refine IsAlgebraic.of_pow two_pos ?_
      -- `a ≠ 0` forces `u = (-b/a) * conj u`, hence `u ^ 2 = (-b/a) * (u * conj u)`
      have key : (a : ℂ) * u ^ 2 = -(b : ℂ) * (u * conj u) := by
        linear_combination u * hab
      have hu2 : u ^ 2 = (a : ℂ)⁻¹ * (-(b : ℂ) * (u * conj u)) := by
        rw [← key, inv_mul_cancel_left₀ ha']
      rw [hu2]
      refine DiazModulus.mem_Qbar_iff.mp
        (mul_mem (inv_mem ?_) (mul_mem (neg_mem ?_) hcQ))
      · exact SubfieldClass.ratCast_mem DiazModulus.Qbar a
      · exact SubfieldClass.ratCast_mem DiazModulus.Qbar b
  -- the second family: `(1, t, t⁻¹)`
  have hyli : LinearIndependent ℚ ![(1 : ℂ), t, t⁻¹] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def, mul_one] at hg
    -- clear the denominator: a relation on `(1, t, t⁻¹)` becomes a quadratic in `t`
    have hq : (g 1 : ℂ) * t ^ 2 + (g 0 : ℂ) * t + (g 2 : ℂ) = 0 := by
      field_simp at hg
      linear_combination hg
    set p : Polynomial ℚ :=
      Polynomial.C (g 1) * Polynomial.X ^ 2 + Polynomial.C (g 0) * Polynomial.X
        + Polynomial.C (g 2) with hp_def
    have hpt : Polynomial.aeval t p = 0 := by
      rw [hp_def]
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
        map_pow, eq_ratCast]
      linear_combination hq
    -- `t` is transcendental, so that polynomial is the zero polynomial
    have hp0 : p = 0 := by
      by_contra hne
      exact httr ⟨p, hne, hpt⟩
    have h2 : g 1 = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 2) hp0
      simpa [hp_def] using this
    have h1 : g 0 = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 1) hp0
      simpa [hp_def] using this
    have h0 : g 2 = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 0) hp0
      simpa [hp_def] using this
    intro i
    fin_cases i <;> assumption
  -- suppose the target exponential were algebraic; then all six of them are
  by_contra hcon
  rw [Transcendental, not_not] at hcon
  have hconj : IsAlgebraic ℚ (Complex.exp ((conj u) ^ 2 / u)) := by
    have hce : ((conj u) ^ 2 / u) = conj (u ^ 2 / conj u) := by
      simp [map_div₀, map_pow]
    rw [hce, Complex.exp_conj]
    exact isAlgebraic_conj hcon
  have hcexp : IsAlgebraic ℚ (Complex.exp (conj u)) := by
    rw [Complex.exp_conj]; exact isAlgebraic_conj hexp
  -- the six products, computed
  have e01 : u * t = u ^ 2 / conj u := by rw [ht_def]; field_simp
  have e02 : u * t⁻¹ = conj u := by rw [ht_def]; field_simp
  have e11 : conj u * t = u := by rw [ht_def]; field_simp
  have e12 : conj u * t⁻¹ = (conj u) ^ 2 / u := by rw [ht_def]; field_simp
  have hall : ∀ (i : Fin 2) (j : Fin 3),
      IsAlgebraic ℚ (Complex.exp (![u, conj u] i * ![(1 : ℂ), t, t⁻¹] j)) := by
    intro i j
    fin_cases i
    · fin_cases j
      · show IsAlgebraic ℚ (Complex.exp (u * 1))
        rw [mul_one]; exact hexp
      · show IsAlgebraic ℚ (Complex.exp (u * t))
        rw [e01]; exact hcon
      · show IsAlgebraic ℚ (Complex.exp (u * t⁻¹))
        rw [e02]; exact hcexp
    · fin_cases j
      · show IsAlgebraic ℚ (Complex.exp (conj u * 1))
        rw [mul_one]; exact hcexp
      · show IsAlgebraic ℚ (Complex.exp (conj u * t))
        rw [e11]; exact hexp
      · show IsAlgebraic ℚ (Complex.exp (conj u * t⁻¹))
        rw [e12]; exact hconj
  obtain ⟨i, j, hij⟩ := hSix ![u, conj u] ![(1 : ℂ), t, t⁻¹] hxli hyli
  exact hij (hall i j)

open DiazModulus in
theorem solution {u : ℂ} (h : IsCandidate u) :
    Transcendental ℚ (Complex.exp (u ^ 2 / conj u)) :=
  core hermite_lindemann_holds six_exponentials h
