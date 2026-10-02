-- Prove2me | solution 1 for DiazModulus.diaz_2007_cor6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:35:42.043454+00:00
-- url     : https://prove2.me/submissions/11b9d9f1-ddeb-4831-a8cd-ff923c7111ae

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_diaz_2007_th4
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable
import Theorems.Thm_DiazModulus_logAlg_conj_stable

/-!
# Diaz 2007, Corollaire 6

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres
algébriques*, JTNB 19 (2007), Corollaire 6 (pp. 385–388).

Both parts are Théorème 4 (`DiazModulus.diaz_2007_th4`) with `x = (1, r)`, `r = l₁/l₀`, and
`y = (l₀, conj l₀)`. Then `x₂/x₁ = r`, and the four products are `l₀`, `conj l₀`, `r l₀ = l₁`
and `r conj l₀ = ± conj l₁`, because `r` lies on an axis, so `conj r = ± r`.

* **1)** Suppose `r ∉ Q̄`. Then `(1, r)` is `Q̄`-free, and `(y₁, y₂, 1/x₁) = (l₀, conj l₀, 1)` is
  free by hypothesis (which also gives `l₀ ≠ 0`). The four products lie in `ℒ̃`, by
  conjugation stability of `ℒ̃`, a contradiction.
* **2)** Suppose `r ∉ ℚ`. Then `(1, r)` is `ℚ`-free, and `(l₀, conj l₀)` is `ℚ`-free because `l₀`
  is off both axes: compare real and imaginary parts. The four products lie in `ℒ`, by
  conjugation stability of `ℒ` and its closure under negation, a contradiction.
-/

open Complex ComplexConjugate

namespace D6_diaz_2007_cor6

open DiazModulus

/-- `ℒ` is closed under negation: `exp (-z) = (exp z)⁻¹`. -/
theorem neg_mem_logAlg {z : ℂ} (h : z ∈ LogAlg) : -z ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (-z))
  rw [Complex.exp_neg]
  exact IsAlgebraic.inv h

/-- On the two axes, conjugation is `± id`. -/
theorem conj_eq_or_eq_neg {r : ℂ} (h : r.im = 0 ∨ r.re = 0) : conj r = r ∨ conj r = -r := by
  rcases h with h | h
  · exact Or.inl (Complex.conj_eq_iff_im.2 h)
  · exact Or.inr (Complex.ext (by simp [h]) (by simp))

/-- `(1, r)` is `Q̄`-free as soon as `r ∉ Q̄`. -/
theorem one_pair_free_of_not_mem_Qbar {r : ℂ} (hr : r ∉ Qbar) :
    ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * 1 + b * r = 0 → a = 0 ∧ b = 0 := by
  intro a b ha hb hab
  by_cases hb0 : b = 0
  · subst hb0
    exact ⟨by simpa using hab, rfl⟩
  · refine absurd ?_ hr
    have e : r = -a / b := by
      rw [eq_div_iff hb0]
      linear_combination hab
    rw [e]
    exact Qbar.div_mem (Qbar.neg_mem ha) hb

/-- `(1, r)` is `ℚ`-free as soon as `r ∉ ℚ`. -/
theorem one_pair_free_of_irrational {r : ℂ} (hr : ∀ q : ℚ, r ≠ q) :
    ∀ p q : ℚ, (p : ℂ) * 1 + (q : ℂ) * r = 0 → p = 0 ∧ q = 0 := by
  intro p q hpq
  by_cases hq0 : q = 0
  · subst hq0
    exact ⟨by simpa using hpq, rfl⟩
  · refine absurd ?_ (hr (-p / q))
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    push_cast
    rw [eq_div_iff hq0']
    linear_combination hpq

/-- `(l, conj l)` is `ℚ`-free when `l` lies off both axes: the real part of a relation reads
`(p + q) re l = 0`, the imaginary part `(p - q) im l = 0`. -/
theorem conj_pair_free {l : ℂ} (hre : l.re ≠ 0) (him : l.im ≠ 0) :
    ∀ p q : ℚ, (p : ℂ) * l + (q : ℂ) * conj l = 0 → p = 0 ∧ q = 0 := by
  intro p q hpq
  have h1 := congrArg Complex.re hpq
  have h2 := congrArg Complex.im hpq
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
    Complex.ratCast_im, Complex.conj_re, Complex.conj_im, Complex.zero_re,
    Complex.zero_im] at h1 h2
  have h1' : ((p : ℝ) + q) * l.re = 0 := by linear_combination h1
  have h2' : ((p : ℝ) - q) * l.im = 0 := by linear_combination h2
  have hs := (mul_eq_zero.1 h1').resolve_right hre
  have hd := (mul_eq_zero.1 h2').resolve_right him
  have hp : (p : ℝ) = 0 := by linear_combination (hs + hd) / 2
  have hq : (q : ℝ) = 0 := by linear_combination (hs - hd) / 2
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hq⟩

end D6_diaz_2007_cor6

open DiazModulus D6_diaz_2007_cor6 in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y)) :
    -- 1)
    (∀ l₀ l₁ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * l₀ + c * conj l₀ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ((l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) → l₁ / l₀ ∈ LogAlgTilde → l₁ / l₀ ∈ Qbar) ∧
    -- 2)
    (∀ l₀ l₁ : ℂ, l₀ ∈ LogAlg → l₁ ∈ LogAlg →
      l₀.re ≠ 0 → l₀.im ≠ 0 → l₁.re ≠ 0 → l₁.im ≠ 0 →
      ((l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) → l₁ / l₀ ∈ LogAlgTilde → ∃ q : ℚ, l₁ / l₀ = q) := by
  obtain ⟨th1, th2⟩ := diaz_2007_th4 hSSE hB
  refine ⟨?_, ?_⟩
  · -- 1) Théorème 4 1) with `x = (1, l₁/l₀)`, `y = (l₀, conj l₀)`
    intro l₀ l₁ h₀ h₁ hfree haxis hr
    by_contra hrQ
    have hl₀ : l₀ ≠ 0 := fun h0 =>
      one_ne_zero (hfree 0 1 0 Qbar.zero_mem Qbar.one_mem Qbar.zero_mem (by rw [h0]; ring)).2.1
    have hl₁ : l₁ / l₀ * l₀ = l₁ := div_mul_cancel₀ l₁ hl₀
    -- `conj (l₁/l₀) * conj l₀ = conj l₁ ∈ ℒ̃`
    have hc₁ := logAlgTilde_conj_stable _ h₁
    rw [← hl₁, map_mul] at hc₁
    refine th1 1 (l₁ / l₀) l₀ (conj l₀) (one_pair_free_of_not_mem_Qbar hrQ) ?_
      (by rwa [div_one])
      ⟨by rwa [one_mul], by rw [one_mul]; exact logAlgTilde_conj_stable _ h₀, by rwa [hl₁], ?_⟩
    · -- `(l₀, conj l₀, 1/1)` is `Q̄`-free
      intro a b c ha hb hc habc
      obtain ⟨hc', ha', hb'⟩ := hfree c a b hc ha hb (by linear_combination habc)
      exact ⟨ha', hb', hc'⟩
    · -- `(l₁/l₀) conj l₀ = ± conj l₁`
      rcases conj_eq_or_eq_neg haxis with e | e
      · rwa [e] at hc₁
      · rw [e, neg_mul] at hc₁
        have h := Submodule.neg_mem _ hc₁
        rwa [neg_neg] at h
  · -- 2) Théorème 4 2) with `x = (1, l₁/l₀)`, `y = (l₀, conj l₀)`
    intro l₀ l₁ h₀ h₁ hre₀ him₀ _ _ haxis hr
    by_contra hrQ
    have hirr : ∀ q : ℚ, l₁ / l₀ ≠ q := fun q hq => hrQ ⟨q, hq⟩
    have hl₀ : l₀ ≠ 0 := fun h0 => hre₀ (by rw [h0, Complex.zero_re])
    have hl₁ : l₁ / l₀ * l₀ = l₁ := div_mul_cancel₀ l₁ hl₀
    -- `conj (l₁/l₀) * conj l₀ = conj l₁ ∈ ℒ`
    have hc₁ := logAlg_conj_stable _ h₁
    rw [← hl₁, map_mul] at hc₁
    refine th2 1 (l₁ / l₀) l₀ (conj l₀) (one_pair_free_of_irrational hirr)
      (conj_pair_free hre₀ him₀) (by rwa [div_one])
      ⟨by rwa [one_mul], by rw [one_mul]; exact logAlg_conj_stable _ h₀, by rwa [hl₁], ?_⟩
    -- `(l₁/l₀) conj l₀ = ± conj l₁`
    rcases conj_eq_or_eq_neg haxis with e | e
    · rwa [e] at hc₁
    · rw [e, neg_mul] at hc₁
      have h := neg_mem_logAlg hc₁
      rwa [neg_neg] at h
