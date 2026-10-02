-- Prove2me | solution 1 for DiazModulus.diaz_2007_th6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:35:48.627717+00:00
-- url     : https://prove2.me/submissions/783cf97a-d3c5-439b-8e7d-82be64e434a1

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable
import Theorems.Thm_DiazModulus_quadratic_eq_zero_of_not_mem_Qbar

/-!
# Diaz 2007, Théorème 6

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques*,
J. Théor. Nombres Bordeaux 19 (2007), p. 389, with his proof, under Roy's strong six exponentials
theorem `hSSE`.

1. `x = (v, v̄)` is free by hypothesis and `y = (1, u, u²)` is free because `u ∉ Q̄`. A non-trivial
   relation `a + b u + c ū = 0` has `c ≠ 0`, so `ū = α + β u` with `α, β ∈ Q̄`. If `v, vu, vu² ∈ ℒ̃`
   then `vū` and `vū²` are in `ℒ̃`, hence so are their conjugates `v̄u`, `v̄u²`, and `v̄`: all six
   products `xᵢyⱼ` lie in `ℒ̃`, against `hSSE`. The hypothesis `v ∉ Q̄` is not used.
2. Part 1 at `u := t`, `v := l/t`: the three products are `l/t`, `l` and `t l`.
3. Part 1 at `u := s`, `v := l`: the three products are `l`, `s l` and `s² l`.
4. `l/l₁ = l₂/l` from `l₁ l₂ = l²`. If `l/l₁ ∉ Q̄`, part 1 at `u := l/l₁`, `v := l₁` gives the
   products `l₁`, `l` and `l²/l₁ = l₂`, all in `ℒ̃`.
-/

open Complex ComplexConjugate

namespace Diaz2007Th6

open DiazModulus

/-- `ℒ̃` is closed under `Q̄`-linear combinations of two of its elements. -/
theorem comb2_mem {a b x y : ℂ} (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hx : x ∈ LogAlgTilde)
    (hy : y ∈ LogAlgTilde) : a * x + b * y ∈ LogAlgTilde :=
  LogAlgTilde.add_mem (LogAlgTilde.smul_mem ⟨a, ha⟩ hx) (LogAlgTilde.smul_mem ⟨b, hb⟩ hy)

/-- `ℒ̃` is closed under `Q̄`-linear combinations of three of its elements. -/
theorem comb3_mem {a b c x y z : ℂ} (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar)
    (hx : x ∈ LogAlgTilde) (hy : y ∈ LogAlgTilde) (hz : z ∈ LogAlgTilde) :
    a * x + b * y + c * z ∈ LogAlgTilde :=
  LogAlgTilde.add_mem (comb2_mem ha hb hx hy) (LogAlgTilde.smul_mem ⟨c, hc⟩ hz)

/-- A pair with no non-trivial `Q̄`-relation is `Q̄`-linearly independent. -/
theorem linInd_pair {x y : ℂ}
    (h : ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * x + b * y = 0 → a = 0 ∧ b = 0) :
    LinearIndependent (↥Qbar) ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  obtain ⟨h1, h2⟩ := h s t s.2 t.2 hst
  exact ⟨Subtype.ext h1, Subtype.ext h2⟩

/-- `1, z, z²` are `Q̄`-linearly independent when `z ∉ Q̄`. -/
theorem linInd_one_sq {z : ℂ} (hz : z ∉ Qbar) : LinearIndependent (↥Qbar) ![1, z, z ^ 2] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  have hg' : (g 0 : ℂ) * 1 + (g 1 : ℂ) * z + (g 2 : ℂ) * z ^ 2 = 0 := hg
  obtain ⟨h2, h1, h0⟩ := quadratic_eq_zero_of_not_mem_Qbar hz (g 2).2 (g 1).2 (g 0).2
    (by linear_combination hg')
  intro i
  fin_cases i
  · exact Subtype.ext h0
  · exact Subtype.ext h1
  · exact Subtype.ext h2

/-- Part 1 without the hypothesis `v ∉ Q̄`, which the argument never uses. -/
theorem core
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u v : ℂ} (hu : u ∉ Qbar)
    (hv : ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * v + b * conj v = 0 → a = 0 ∧ b = 0)
    (hdep : ∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
      a + b * u + c * conj u = 0) :
    ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * u ^ 2 ∈ LogAlgTilde) := by
  rintro ⟨h0, h1, h2⟩
  obtain ⟨a, b, c, ha, hb, hc, hne, habc⟩ := hdep
  -- the coefficient of `ū` is non-zero, since `1, u` are free
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨-, hb0, ha0⟩ := quadratic_eq_zero_of_not_mem_Qbar hu Qbar.zero_mem hb ha
      (by linear_combination habc)
    exact hne ⟨ha0, hb0, rfl⟩
  -- `ū = α + β u`
  have hα : -a / c ∈ Qbar := Qbar.div_mem (Qbar.neg_mem ha) hc
  have hβ : -b / c ∈ Qbar := Qbar.div_mem (Qbar.neg_mem hb) hc
  have hconj : conj u = -a / c + -b / c * u := by
    field_simp
    linear_combination habc
  -- `v ū` and `v ū²` are in `ℒ̃`
  have h3 : v * conj u ∈ LogAlgTilde := by
    have := comb2_mem hα hβ h0 h1
    rw [hconj]
    convert this using 1
    ring
  have h4 : v * conj u ^ 2 ∈ LogAlgTilde := by
    have := comb3_mem (Qbar.mul_mem hα hα) (Qbar.add_mem (Qbar.mul_mem hα hβ)
      (Qbar.mul_mem hα hβ)) (Qbar.mul_mem hβ hβ) h0 h1 h2
    rw [hconj]
    convert this using 1
    ring
  -- and so are the conjugates `v̄`, `v̄ u`, `v̄ u²`
  have h5 : conj v ∈ LogAlgTilde := logAlgTilde_conj_stable v h0
  have h6 : conj v * u ∈ LogAlgTilde := by
    simpa using logAlgTilde_conj_stable _ h3
  have h7 : conj v * u ^ 2 ∈ LogAlgTilde := by
    simpa using logAlgTilde_conj_stable _ h4
  -- all six products of `x = (v, v̄)` and `y = (1, u, u²)` are in `ℒ̃`
  refine hSSE ![v, conj v] ![1, u, u ^ 2] (linInd_pair hv) (linInd_one_sq hu) ?_
  intro i j
  fin_cases i <;> fin_cases j
  · show v * 1 ∈ LogAlgTilde
    rw [mul_one]; exact h0
  · exact h1
  · exact h2
  · show conj v * 1 ∈ LogAlgTilde
    rw [mul_one]; exact h5
  · exact h6
  · exact h7

end Diaz2007Th6

open DiazModulus Diaz2007Th6 in
/-- **Diaz 2007, Théorème 6**, parts 1)–4), under Roy's strong six exponentials theorem `hSSE`. -/
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- 1)
    (∀ u v : ℂ, u ∉ Qbar → v ∉ Qbar →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * v + b * conj v = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * u + c * conj u = 0) →
      ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * u ^ 2 ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ l t : ℂ, l ∈ LogAlgTilde → t ∉ Qbar →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * (l / t) + b * conj (l / t) = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * t + c * conj t = 0) →
      ¬ (t * l ∈ LogAlgTilde ∧ l / t ∈ LogAlgTilde)) ∧
    -- 3)
    (∀ l s : ℂ, l ∈ LogAlgTilde → s ∉ Qbar →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l + b * conj l = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * s + c * conj s = 0) →
      ¬ (s * l ∈ LogAlgTilde ∧ s ^ 2 * l ∈ LogAlgTilde)) ∧
    -- 4)
    (∀ l l₁ l₂ : ℂ, l ∈ LogAlgTilde → l₁ ∈ LogAlgTilde → l₂ ∈ LogAlgTilde →
      l ≠ 0 → l₁ ≠ 0 → l₂ ≠ 0 → l₁ * l₂ = l ^ 2 →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l₁ + b * conj l₁ = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * (l / l₁) + c * conj (l / l₁) = 0) →
      l / l₁ = l₂ / l ∧ l / l₁ ∈ Qbar) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1)
    intro u v hu _ hv hdep
    exact core hSSE hu hv hdep
  · -- 2) part 1 at `u := t`, `v := l / t`
    rintro l t hl ht hv hdep ⟨htl, hlt⟩
    have ht0 : t ≠ 0 := fun h => ht (h ▸ Qbar.zero_mem)
    refine core hSSE ht hv hdep ⟨hlt, ?_, ?_⟩
    · have : l / t * t = l := by field_simp
      rw [this]; exact hl
    · have : l / t * t ^ 2 = t * l := by field_simp
      rw [this]; exact htl
  · -- 3) part 1 at `u := s`, `v := l`
    rintro l s hl hs hv hdep ⟨hsl, hssl⟩
    refine core hSSE hs hv hdep ⟨hl, ?_, ?_⟩
    · rw [mul_comm]; exact hsl
    · rw [mul_comm]; exact hssl
  · -- 4) part 1 at `u := l / l₁`, `v := l₁`
    intro l l₁ l₂ hl hl₁ hl₂ hl0 hl₁0 _ hprod hv hdep
    refine ⟨?_, ?_⟩
    · rw [div_eq_div_iff hl₁0 hl0]
      linear_combination -hprod
    · by_contra hq
      refine core hSSE hq hv hdep ⟨hl₁, ?_, ?_⟩
      · have : l₁ * (l / l₁) = l := by field_simp
        rw [this]; exact hl
      · have : l₁ * (l / l₁) ^ 2 = l₂ := by
          field_simp
          linear_combination -hprod
        rw [this]; exact hl₂
