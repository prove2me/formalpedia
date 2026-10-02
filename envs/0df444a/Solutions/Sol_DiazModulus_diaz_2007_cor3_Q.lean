-- Prove2me | solution 1 for DiazModulus.diaz_2007_cor3_Q
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:35:33.423483+00:00
-- url     : https://prove2.me/submissions/f1490ba6-1495-4624-b563-751425c046aa

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlg_conj_stable
import Theorems.Thm_DiazModulus_strong_six_exponentials_iff_quotient_form
import Theorems.Thm_DiazModulus_diaz_2007_cor1_PQ
import Theorems.Thm_DiazModulus_diaz_2007_cor2_P_consequences

/-!
# Diaz 2007, Corollaire 3 (Q)

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques*,
J. Théor. Nombres Bordeaux 19 (2007), p. 382, with his proof.

1. The quotient form of the strong six exponentials theorem with `λ₁ = 1`.
2. Corollaire 1 (PQ) 1) with `λ₁ = 1`: `1/λ₀` lies on an axis when `λ₀` does.
3. If `ℓ = λ₂/λ₀ ∈ ℒ`, then `ℓ` and `ℓ̄ = ±λ̄₂/λ₀` are `ℚ`-independent, because `λ₂` is off both axes;
   Baker's theorem makes `1, ℓ, ℓ̄` free over `Q̄`, and Corollaire 2 (P) 2) at `(λ₀, ℓ)` puts
   `λ₀ℓ = λ₂` outside `ℒ̃`, against the hypothesis.
-/

open Complex ComplexConjugate

namespace DiazCor3Q

open DiazModulus

theorem one_mem : (1 : ℂ) ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert _ _)

theorem mem_of_log {z : ℂ} (h : z ∈ LogAlg) : z ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert_of_mem _ h)

end DiazCor3Q

open DiazModulus DiazCor3Q in
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
    (∀ l₀ l₂ l₃ : ℂ, l₀ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde → l₃ ∈ LogAlgTilde → l₀ ∉ Qbar →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * l₃ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₂ / l₀ ∈ LogAlgTilde ∧ l₃ / l₀ ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ l₀ l₂ : ℂ, l₀ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (l₀.im = 0 ∨ l₀.re = 0) → l₀ ∉ Qbar →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l₀ + b * l₂ + c * conj l₂ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      l₂ / l₀ ∉ LogAlgTilde) ∧
    -- 3)
    (∀ l₀ l₂ : ℂ, l₀ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      (l₀.im = 0 ∨ l₀.re = 0) → l₀ ∉ Qbar → l₂.re ≠ 0 → l₂.im ≠ 0 →
      l₂ / l₀ ∉ LogAlg) := by
  have hV3 := strong_six_exponentials_iff_quotient_form.mp hSSE
  have hP1 := (diaz_2007_cor1_PQ hSSE).1
  have hP2 := (diaz_2007_cor2_P_consequences hSSE).1
  -- `(l₀, 1)` is free when `l₀ ∉ Q̄`
  have pair_one : ∀ l₀ : ℂ, l₀ ∉ Qbar →
      ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₀ + b * 1 = 0 → a = 0 ∧ b = 0 := by
    intro l₀ hl₀ a b ha hb hab
    by_cases ha0 : a = 0
    · exact ⟨ha0, by simpa [ha0] using hab⟩
    · exfalso; apply hl₀
      have : l₀ = -b / a := by field_simp; linear_combination hab
      rw [this]; exact Qbar.div_mem (Qbar.neg_mem hb) ha
  refine ⟨?_, ?_, ?_⟩
  · -- 1)
    intro l₀ l₂ l₃ h₀ h₂ h₃ hQ hfree
    have := hV3 l₀ 1 l₂ l₃ h₀ one_mem h₂ h₃ (pair_one l₀ hQ) hfree
    simpa only [one_mul] using this
  · -- 2)
    intro l₀ l₂ h₀ h₂ hax hQ hfree
    have hl₀ : l₀ ≠ 0 := fun h => hQ (h ▸ Qbar.zero_mem)
    have hax' : ((1 : ℂ) / l₀).im = 0 ∨ ((1 : ℂ) / l₀).re = 0 := by
      rw [one_div]
      rcases hax with h | h
      · left; simp [Complex.inv_im, h]
      · right; simp [Complex.inv_re, h]
    have hQ' : (1 : ℂ) / l₀ ∉ Qbar := by
      intro h; apply hQ
      have := Qbar.inv_mem h
      rwa [one_div, inv_inv] at this
    have := hP1 l₀ 1 l₂ h₀ one_mem h₂ hfree hax' hQ'
    simpa only [one_mul] using this
  · -- 3)
    intro l₀ l₂ h₀ h₂ hax hQ hre him hl
    have hl₀ : l₀ ≠ 0 := fun h => hQ (h ▸ Qbar.zero_mem)
    set ℓ := l₂ / l₀ with hℓ
    have hlc : conj ℓ ∈ LogAlg := logAlg_conj_stable ℓ hl
    -- `conj l₀ = ± l₀`
    obtain ⟨s, hs, hcs⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ conj l₀ = s * l₀ := by
      rcases hax with h | h
      · exact ⟨1, Or.inl rfl, by rw [one_mul]; exact Complex.conj_eq_iff_im.mpr h⟩
      · refine ⟨-1, Or.inr rfl, ?_⟩
        apply Complex.ext <;> simp [h]
    -- `ℓ` and `ℓ̄` are `ℚ`-independent
    have hfreeQ : ∀ p q : ℚ, (p : ℂ) * ℓ + (q : ℂ) * conj ℓ = 0 → p = 0 ∧ q = 0 := by
      intro p q hpq
      have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
      have h1 : (p : ℂ) * l₂ + ((q : ℂ) / s) * conj l₂ = 0 := by
        have hcl : conj ℓ = conj l₂ / (s * l₀) := by rw [hℓ, map_div₀, hcs]
        rw [hcl, hℓ] at hpq
        have e : (p : ℂ) * l₂ + ((q : ℂ) / s) * conj l₂
            = ((p : ℂ) * (l₂ / l₀) + (q : ℂ) * (conj l₂ / (s * l₀))) * l₀ := by
          field_simp
        rw [e, hpq, zero_mul]
      obtain ⟨q', hq', h1'⟩ : ∃ q' : ℚ, (q' = q ∨ q' = -q) ∧ (p : ℂ) * l₂ + (q' : ℂ) * conj l₂ = 0 := by
        rcases hs with rfl | rfl
        · exact ⟨q, Or.inl rfl, by rw [← h1]; ring⟩
        · exact ⟨-q, Or.inr rfl, by rw [← h1]; push_cast; ring⟩
      have hre' := congrArg Complex.re h1'
      have him' := congrArg Complex.im h1'
      simp only [Complex.add_re, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
        Complex.conj_re, Complex.conj_im, Complex.zero_re, zero_mul, sub_zero] at hre'
      simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
        Complex.conj_re, Complex.conj_im, Complex.zero_im, zero_mul, add_zero] at him'
      have e1 : ((p : ℝ) + q') * l₂.re = 0 := by linear_combination hre'
      have e2 : ((p : ℝ) - q') * l₂.im = 0 := by linear_combination him'
      have f1 : (p : ℝ) + q' = 0 := (mul_eq_zero.mp e1).resolve_right hre
      have f2 : (p : ℝ) - q' = 0 := (mul_eq_zero.mp e2).resolve_right him
      have hp : (p : ℝ) = 0 := by linarith
      have hq0 : (q' : ℝ) = 0 := by linarith
      have hp' : p = 0 := by exact_mod_cast hp
      have hq0' : q' = 0 := by exact_mod_cast hq0
      refine ⟨hp', ?_⟩
      rcases hq' with h | h
      · rw [← h]; exact hq0'
      · have : -q = 0 := h ▸ hq0'
        linarith
    -- Baker: `1, ℓ, ℓ̄` are free over `Q̄`
    have hfree3 : ∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * ℓ + c * conj ℓ = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 := by
      intro a b c ha hb hc habc
      by_cases hbc : b = 0 ∧ c = 0
      · refine ⟨?_, hbc.1, hbc.2⟩
        simpa [hbc.1, hbc.2] using habc
      · exfalso
        refine hB ℓ (conj ℓ) b c hl hlc hfreeQ (mem_Qbar_iff.mp hb) (mem_Qbar_iff.mp hc) hbc ?_
        have : b * ℓ + c * conj ℓ = -a := by linear_combination habc
        rw [this]
        exact (mem_Qbar_iff.mp ha).neg
    have hout := hP2 l₀ ℓ h₀ (mem_of_log hl) hax hQ hfree3
    apply hout
    have : l₀ * ℓ = l₂ := by rw [hℓ]; field_simp
    rw [this]; exact h₂
