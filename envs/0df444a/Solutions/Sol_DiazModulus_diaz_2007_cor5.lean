-- Prove2me | solution 1 for DiazModulus.diaz_2007_cor5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:02:00.795486+00:00
-- url     : https://prove2.me/submissions/85eba034-a569-464b-910a-bee80b0b6bd3

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable
import Theorems.Thm_DiazModulus_quadratic_eq_zero_of_not_mem_Qbar
import Theorems.Thm_DiazModulus_diaz_2007_cor4

/-!
# Diaz 2007, Corollaire 5

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres
algébriques*, JTNB 19 (2007), Corollaire 5, p. 383, with the proof on pp. 383–384.

Fix `l ∈ ℒ̃ ∖ Q̄`. Everything comes from Corollaire 4 (`diaz_2007_cor4`), conjugation
stability of `ℒ̃`, and the quadratic lemma for a transcendental `l`.

* **1)** Corollaire 4, part 2, at `(l, conj l)`; the two quotients are conjugate.
* **2)** Corollaire 4, part 3, at `(l, conj l)`; again the two quotients are conjugate.
* **3)** A non-trivial relation `a + b l + c conj l = 0` gives `conj l = α + β l` with
  `α, β ∈ Q̄ ∖ {0}`. Then `(l, conj l, l conj l)` is free, since a relation becomes a quadratic
  equation in `l`. By part 1, `conj l / l = β + α (1/l)` is not in `ℒ̃`, so neither is `1/l`.
* **4)** Corollaire 4, part 2, at `(l, l + α)`; the triple `(l, l + α, l (l + α))` is free by
  the quadratic lemma, and `(l + α)/l = 1 + α (1/l)`, `l/(l + α) = 1 - α (1/(l + α))`.
-/

open Complex ComplexConjugate

namespace D5_diaz_2007_cor5

open DiazModulus

/-- `1 ∈ ℒ̃`. -/
theorem one_mem_logAlgTilde : (1 : ℂ) ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert _ _)

/-- `ℒ̃` is a `Q̄`-module: `c * z ∈ ℒ̃` for `c ∈ Q̄` and `z ∈ ℒ̃`. -/
theorem mul_mem_logAlgTilde {c z : ℂ} (hc : c ∈ Qbar) (hz : z ∈ LogAlgTilde) :
    c * z ∈ LogAlgTilde :=
  Submodule.smul_mem LogAlgTilde (⟨c, hc⟩ : ↥Qbar) hz

/-- `Q̄` is stable under complex conjugation. -/
theorem conj_mem_Qbar {z : ℂ} (hz : z ∈ Qbar) : conj z ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 hz).algHom
    ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ))

end D5_diaz_2007_cor5

open DiazModulus D5_diaz_2007_cor5 in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {l : ℂ} (hl : l ∈ LogAlgTilde) (hlQ : l ∉ Qbar) :
    -- 1)
    ((∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a * l + b * conj l + c * (l * conj l) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      l / conj l ∉ LogAlgTilde) ∧
    -- 2)
    ((∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l + b * conj l = 0 → a = 0 ∧ b = 0) →
      l ^ 2 / conj l ∉ LogAlgTilde) ∧
    -- 3)
    ((∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * l + b * conj l = 0 → a = 0 ∧ b = 0) →
      (∃ a b c : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
        a + b * l + c * conj l = 0) →
      1 / l ∉ LogAlgTilde) ∧
    -- 4)
    (∀ α : ℂ, α ∈ Qbar → α ≠ 0 → ¬ (1 / l ∈ LogAlgTilde ∧ 1 / (l + α) ∈ LogAlgTilde)) := by
  obtain ⟨-, c4₂, c4₃, -⟩ := diaz_2007_cor4 hSSE
  have hcl : conj l ∈ LogAlgTilde := logAlgTilde_conj_stable l hl
  have hl0 : l ≠ 0 := fun h0 => hlQ (by rw [h0]; exact Qbar.zero_mem)
  -- 1) Corollaire 4, part 2, at `(l, conj l)`: the two quotients are conjugate
  have part1 : (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar →
      a * l + b * conj l + c * (l * conj l) = 0 → a = 0 ∧ b = 0 ∧ c = 0) →
      l / conj l ∉ LogAlgTilde := by
    intro hfree h
    have hc := logAlgTilde_conj_stable _ h
    rw [map_div₀, conj_conj] at hc
    exact c4₂ l (conj l) hl hcl hfree ⟨h, hc⟩
  refine ⟨part1, ?_, ?_, ?_⟩
  · -- 2) Corollaire 4, part 3, at `(l, conj l)`: the two quotients are conjugate
    intro hfree h
    have hc := logAlgTilde_conj_stable _ h
    rw [map_div₀, map_pow, conj_conj] at hc
    exact c4₃ l (conj l) hl hcl hfree ⟨h, hc⟩
  · -- 3)
    rintro hfree ⟨a, b, c, ha, hb, hc, hne, habc⟩ hinv
    -- `c ≠ 0`: otherwise `l ∈ Q̄`, or the relation is trivial
    have hc0 : c ≠ 0 := by
      rintro rfl
      by_cases hb0 : b = 0
      · subst hb0
        exact hne ⟨by linear_combination habc, rfl, rfl⟩
      · apply hlQ
        rw [eq_div_of_mul_eq hb0 (by linear_combination habc : l * b = -a)]
        exact Qbar.div_mem (Qbar.neg_mem ha) hb
    -- `conj l = α + β l` with `α = -a/c`, `β = -b/c`
    obtain ⟨α, β, hαQ, hβQ, hconj⟩ :
        ∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ conj l = α + β * l := by
      refine ⟨-a / c, -b / c, Qbar.div_mem (Qbar.neg_mem ha) hc,
        Qbar.div_mem (Qbar.neg_mem hb) hc, ?_⟩
      rw [eq_div_of_mul_eq hc0 (by linear_combination habc : conj l * c = -a - b * l)]
      ring
    -- `α ≠ 0`, since `(l, conj l)` is free
    have hα0 : α ≠ 0 := by
      rintro rfl
      exact one_ne_zero (neg_eq_zero.1 (hfree β (-1) hβQ (Qbar.neg_mem Qbar.one_mem)
        (by rw [hconj]; ring)).2)
    -- `β ≠ 0`, since otherwise `l = conj α ∈ Q̄`
    have hβ0 : β ≠ 0 := by
      rintro rfl
      have e : conj (conj l) = conj α := by rw [hconj, zero_mul, add_zero]
      rw [conj_conj] at e
      exact hlQ (e ▸ conj_mem_Qbar hαQ)
    -- `(l, conj l, l conj l)` is free: a relation is a quadratic equation in `l`
    have hfree3 : ∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar →
        a * l + b * conj l + c * (l * conj l) = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
      intro a' b' c' ha' hb' hc' h
      rw [hconj] at h
      obtain ⟨q₂, q₁, q₀⟩ := quadratic_eq_zero_of_not_mem_Qbar hlQ (Qbar.mul_mem hc' hβQ)
        (Qbar.add_mem (Qbar.add_mem ha' (Qbar.mul_mem hb' hβQ)) (Qbar.mul_mem hc' hαQ))
        (Qbar.mul_mem hb' hαQ)
        (by linear_combination h : (c' * β) * l ^ 2 + (a' + b' * β + c' * α) * l + b' * α = 0)
      have hc'0 : c' = 0 := (mul_eq_zero.1 q₂).resolve_right hβ0
      have hb'0 : b' = 0 := (mul_eq_zero.1 q₀).resolve_right hα0
      refine ⟨?_, hb'0, hc'0⟩
      rw [hc'0, hb'0] at q₁
      simpa using q₁
    -- `conj l / l = β + α (1/l)` would lie in `ℒ̃`, and so would its conjugate `l / conj l`
    apply part1 hfree3
    have hq : conj l / l ∈ LogAlgTilde := by
      have e : conj l / l = β * 1 + α * (1 / l) := by
        rw [hconj]
        field_simp
        ring
      rw [e]
      exact add_mem (mul_mem_logAlgTilde hβQ one_mem_logAlgTilde) (mul_mem_logAlgTilde hαQ hinv)
    have hc := logAlgTilde_conj_stable _ hq
    rwa [map_div₀, conj_conj] at hc
  · -- 4) Corollaire 4, part 2, at `(l, l + α)`
    rintro α hα hα0 ⟨h₁, h₂⟩
    have hlα : l + α ≠ 0 := by
      intro h0
      apply hlQ
      rw [show l = -α by linear_combination h0]
      exact Qbar.neg_mem hα
    have hαL : α ∈ LogAlgTilde := by
      simpa using mul_mem_logAlgTilde hα one_mem_logAlgTilde
    refine c4₂ l (l + α) hl (add_mem hl hαL) ?_ ⟨?_, ?_⟩
    · -- `(l, l + α, l (l + α))` is free: a relation is a quadratic equation in `l`
      intro a b c ha hb hc h
      obtain ⟨q₂, q₁, q₀⟩ := quadratic_eq_zero_of_not_mem_Qbar hlQ hc
        (Qbar.add_mem (Qbar.add_mem ha hb) (Qbar.mul_mem hc hα)) (Qbar.mul_mem hb hα)
        (by linear_combination h : c * l ^ 2 + (a + b + c * α) * l + b * α = 0)
      have hb0 : b = 0 := (mul_eq_zero.1 q₀).resolve_right hα0
      refine ⟨?_, hb0, q₂⟩
      rw [q₂, hb0] at q₁
      simpa using q₁
    · -- `l / (l + α) = 1 - α (1/(l + α))`
      have e : l / (l + α) = 1 - α * (1 / (l + α)) := by
        field_simp
        ring
      rw [e]
      exact sub_mem one_mem_logAlgTilde (mul_mem_logAlgTilde hα h₂)
    · -- `(l + α) / l = 1 + α (1/l)`
      have e : (l + α) / l = 1 + α * (1 / l) := by
        field_simp
      rw [e]
      exact add_mem one_mem_logAlgTilde (mul_mem_logAlgTilde hα h₁)
