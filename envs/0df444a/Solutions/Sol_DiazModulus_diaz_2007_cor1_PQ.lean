-- Prove2me | solution 1 for DiazModulus.diaz_2007_cor1_PQ
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:10:17.315581+00:00
-- url     : https://prove2.me/submissions/ebbc69b4-9342-4ed0-b492-dddfa8efa52a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_strong_six_exponentials_iff_quotient_form
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable
import Theorems.Thm_DiazModulus_quadratic_eq_zero_of_not_mem_Qbar

open Complex ComplexConjugate

namespace DiazCor1PQ

theorem one_mem_logAlgTilde : (1 : ℂ) ∈ DiazModulus.LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert _ _)

/-- A pair `(l₀, l₁)` with `l₀ ≠ 0` and `l₁ / l₀ ∉ Q̄` is free over `Q̄`. -/
theorem pair_free {l₀ l₁ : ℂ} (h₀ : l₀ ≠ 0) (hq : l₁ / l₀ ∉ DiazModulus.Qbar) :
    ∀ a b : ℂ, a ∈ DiazModulus.Qbar → b ∈ DiazModulus.Qbar → a * l₀ + b * l₁ = 0 →
      a = 0 ∧ b = 0 := by
  intro a b ha hb h
  by_cases hb0 : b = 0
  · subst hb0
    exact ⟨(mul_eq_zero.1 (by simpa using h)).resolve_right h₀, rfl⟩
  · refine absurd ?_ hq
    rw [show l₁ / l₀ = -a / b by field_simp; linear_combination h]
    exact div_mem (neg_mem ha) hb

/-- A purely imaginary complex number is the opposite of its conjugate. -/
theorem conj_eq_neg_of_re_eq_zero {z : ℂ} (hz : z.re = 0) : conj z = -z :=
  Complex.ext (by simp [hz]) (by simp)

end DiazCor1PQ

open DiazModulus DiazCor1PQ in
/-- Diaz (2007), Corollaire 1 (PQ), parts 1)–4), each by one application of `hSSE` in quotient
form (version 3) to a suitable quadruple `(l₀, l₁, l₂, l₃)`. -/
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- 1)
    (∀ l₀ l₁ l₂ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * conj l₂ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ((l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) → l₁ / l₀ ∉ Qbar →
      l₁ * l₂ / l₀ ∉ LogAlgTilde) ∧
    -- 2)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₁ + b * l₂ + c * (l₁ * l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ ∈ LogAlgTilde ∧ l₁ / l₂ ∈ LogAlgTilde)) ∧
    -- 3)
    (∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde → l₂ ≠ 0 →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * l₁ + c * (1 / l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ ∈ LogAlgTilde ∧ 1 / l₂ ∈ LogAlgTilde)) ∧
    (∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar → ¬ (l ^ 2 ∈ LogAlgTilde ∧ 1 / l ∈ LogAlgTilde)) ∧
    -- 4)
    (∀ l₀ l₁ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ ^ 2 + b * l₁ + c * (l₀ * l₁) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ / l₀ ∈ LogAlgTilde ∧ l₁ / l₀ ^ 2 ∈ LogAlgTilde)) ∧
    (∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar →
      ¬ (1 / l ∈ LogAlgTilde ∧ 1 / l ^ 2 ∈ LogAlgTilde)) := by
  -- version 3: for `(l₀, l₁)` and `(l₀, l₂, l₃)` free, not both `l₁ l₂ / l₀`, `l₁ l₃ / l₀` in `ℒ̃`
  have hV3 := strong_six_exponentials_iff_quotient_form.mp hSSE
  -- 1) version 3 on `(l₀, l₁, l₂, l̄₂)`; `l₁ l̄₂ / l₀ = ± conj (l₁ l₂ / l₀)` as `l₁ / l₀` is
  -- real or purely imaginary
  have h1 : ∀ l₀ l₁ l₂ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * conj l₂ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ((l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) → l₁ / l₀ ∉ Qbar →
      l₁ * l₂ / l₀ ∉ LogAlgTilde := by
    intro l₀ l₁ l₂ h₀ h₁ h₂ hfree hr hq hmem
    have hl₀ : l₀ ≠ 0 := by
      rintro rfl
      exact one_ne_zero (hfree 1 0 0 (one_mem _) (zero_mem _) (zero_mem _) (by simp)).1
    have key : l₁ * conj l₂ / l₀ ∈ LogAlgTilde := by
      have hc := logAlgTilde_conj_stable _ hmem
      rw [mul_div_right_comm, map_mul] at hc
      rw [mul_div_right_comm]
      rcases hr with hr | hr
      · rwa [conj_eq_iff_im.mpr hr] at hc
      · rw [conj_eq_neg_of_re_eq_zero hr, neg_mul] at hc
        simpa using LogAlgTilde.neg_mem hc
    exact hV3 l₀ l₁ l₂ (conj l₂) h₀ h₁ h₂ (logAlgTilde_conj_stable _ h₂) (pair_free hl₀ hq)
      hfree ⟨hmem, key⟩
  -- 2) version 3 on `(l₁ l₂, l₁, l₂, l₁)`: the quotients are `1` and `l₁ / l₂`
  have h2 : ∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₁ + b * l₂ + c * (l₁ * l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ ∈ LogAlgTilde ∧ l₁ / l₂ ∈ LogAlgTilde) := by
    rintro l₁ l₂ h₁ h₂ hfree ⟨h12, hq⟩
    have hl₁ : l₁ ≠ 0 := by
      rintro rfl
      exact one_ne_zero (hfree 1 0 0 (one_mem _) (zero_mem _) (zero_mem _) (by simp)).1
    have hl₂ : l₂ ≠ 0 := by
      rintro rfl
      exact one_ne_zero (hfree 0 1 0 (zero_mem _) (one_mem _) (zero_mem _) (by simp)).2.1
    refine hV3 (l₁ * l₂) l₁ l₂ l₁ h12 h₁ h₂ h₁ ?_ ?_ ⟨?_, ?_⟩
    · intro a b ha hb h
      have := hfree b 0 a hb (zero_mem _) ha (by linear_combination h)
      exact ⟨this.2.2, this.1⟩
    · intro a b c ha hb hc h
      have := hfree c b a hc hb ha (by linear_combination h)
      exact ⟨this.2.2, this.2.1, this.1⟩
    · rw [div_self (mul_ne_zero hl₁ hl₂)]
      exact one_mem_logAlgTilde
    · rwa [mul_div_mul_left _ _ hl₁]
  -- 3) version 3 on `(1 / l₂, 1, l₁, 1)`: the quotients are `l₁ l₂` and `l₂`
  have h3 : ∀ l₁ l₂ : ℂ, l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde → l₂ ≠ 0 →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * l₁ + c * (1 / l₂) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ ∈ LogAlgTilde ∧ 1 / l₂ ∈ LogAlgTilde) := by
    rintro l₁ l₂ h₁ h₂ - hfree ⟨h12, hinv⟩
    refine hV3 (1 / l₂) 1 l₁ 1 hinv one_mem_logAlgTilde h₁ one_mem_logAlgTilde ?_ ?_ ⟨?_, ?_⟩
    · intro a b ha hb h
      have := hfree b 0 a hb (zero_mem _) ha (by linear_combination h)
      exact ⟨this.2.2, this.1⟩
    · intro a b c ha hb hc h
      have := hfree c b a hc hb ha (by linear_combination h)
      exact ⟨this.2.2, this.2.1, this.1⟩
    · rwa [one_mul, div_div_eq_mul_div, div_one]
    · rwa [one_mul, one_div_one_div]
  -- 3) in particular, `l₁ = l₂ = l`: `(1, l, 1 / l)` is free since `l` is not quadratic over `Q̄`
  have h3' : ∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar →
      ¬ (l ^ 2 ∈ LogAlgTilde ∧ 1 / l ∈ LogAlgTilde) := by
    intro l hl hlq
    have hl0 : l ≠ 0 := fun h => hlq (h ▸ zero_mem _)
    rw [sq]
    refine h3 l l hl hl hl0 fun a b c ha hb hc h => ?_
    have e : c * (1 / l) * l = c := by field_simp
    have := quadratic_eq_zero_of_not_mem_Qbar hlq hb ha hc (by linear_combination l * h - e)
    exact ⟨this.2.1, this.1, this.2.2⟩
  -- 4) version 3 on `(1, l₀, l₁ / l₀, l₁ / l₀²)`: the quotients are `l₁` and `l₁ / l₀`
  have h4 : ∀ l₀ l₁ : ℂ, l₀ ∈ LogAlgTilde → l₁ ∈ LogAlgTilde →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ ^ 2 + b * l₁ + c * (l₀ * l₁) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ / l₀ ∈ LogAlgTilde ∧ l₁ / l₀ ^ 2 ∈ LogAlgTilde) := by
    rintro l₀ l₁ h₀ h₁ hfree ⟨hq1, hq2⟩
    have hl₀ : l₀ ≠ 0 := by
      rintro rfl
      exact one_ne_zero (hfree 1 0 0 (one_mem _) (zero_mem _) (zero_mem _) (by simp)).1
    -- `l₀ ∉ Q̄`, else `0 · l₀² + (-l₀) l₁ + 1 · (l₀ l₁) = 0` is a non-trivial relation
    have hl₀q : l₀ / 1 ∉ Qbar := by
      rw [div_one]
      intro h
      exact one_ne_zero (hfree 0 (-l₀) 1 (zero_mem _) (neg_mem h) (one_mem _) (by ring)).2.2
    refine hV3 1 l₀ (l₁ / l₀) (l₁ / l₀ ^ 2) one_mem_logAlgTilde h₀ hq1 hq2
      (pair_free one_ne_zero hl₀q) ?_ ⟨?_, ?_⟩
    · -- multiply the relation by `l₀²`
      intro a b c ha hb hc h
      have e1 : b * (l₁ / l₀) * l₀ ^ 2 = b * (l₀ * l₁) := by field_simp
      have e2 : c * (l₁ / l₀ ^ 2) * l₀ ^ 2 = c * l₁ := by field_simp
      have := hfree a c b ha hc hb (by linear_combination l₀ ^ 2 * h - e1 - e2)
      exact ⟨this.1, this.2.2, this.2.1⟩
    · rwa [show l₀ * (l₁ / l₀) / 1 = l₁ by field_simp]
    · rwa [show l₀ * (l₁ / l₀ ^ 2) / 1 = l₁ / l₀ by field_simp]
  -- 4) in particular, `l₀ = l`, `l₁ = 1`: `(l², 1, l)` is free since `l` is not quadratic
  have h4' : ∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar →
      ¬ (1 / l ∈ LogAlgTilde ∧ 1 / l ^ 2 ∈ LogAlgTilde) := by
    intro l hl hlq
    refine h4 l 1 hl one_mem_logAlgTilde fun a b c ha hb hc h => ?_
    have := quadratic_eq_zero_of_not_mem_Qbar hlq ha hc hb (by linear_combination h)
    exact ⟨this.1, this.2.2, this.2.1⟩
  exact ⟨h1, h2, h3, h3', h4, h4'⟩
