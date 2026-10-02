-- Prove2me | solution 1 for DiazModulus.diaz_2007_th7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:35:51.787922+00:00
-- url     : https://prove2.me/submissions/8fb01f4e-8309-44b0-982c-ab9f2602dbd7

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable
import Theorems.Thm_DiazModulus_quadratic_eq_zero_of_not_mem_Qbar

/-!
# Diaz 2007, Théorème 7

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques*,
J. Théor. Nombres Bordeaux 19 (2007), p. 390, with his proof, under Roy's strong six exponentials
theorem `hSSE`.

1. `x = (v, v̄)` and `y = (1, u, ū)` are free by hypothesis. If `v, vu, vū ∈ ℒ̃`, their conjugates
   `v̄`, `v̄ū`, `v̄u` are in `ℒ̃` too, so all six products `xᵢyⱼ` are, against `hSSE`.
2. `x = (v, vu)` is free since `v ≠ 0` and `u ∉ Q̄`, and `y = (1, u, u²)` is free since `u ∉ Q̄`.
   The six products are `v, vu, vu², vu, vu², vu³`.
3. The "in particular": part 2 with `v = 1`, as `1 ∈ ℒ̃`.
-/

open Complex ComplexConjugate

namespace Diaz2007Th7

open DiazModulus

/-- `1 ∈ ℒ̃`. -/
theorem one_mem_logAlgTilde : (1 : ℂ) ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert _ _)

/-- A pair with no non-trivial `Q̄`-relation is `Q̄`-linearly independent. -/
theorem linInd_pair {x y : ℂ}
    (h : ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * x + b * y = 0 → a = 0 ∧ b = 0) :
    LinearIndependent (↥Qbar) ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  obtain ⟨h1, h2⟩ := h s t s.2 t.2 hst
  exact ⟨Subtype.ext h1, Subtype.ext h2⟩

/-- A triple `1, y, z` with no non-trivial `Q̄`-relation is `Q̄`-linearly independent. -/
theorem linInd_one_triple {y z : ℂ}
    (h : ∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * y + c * z = 0 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    LinearIndependent (↥Qbar) ![1, y, z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  have hg' : (g 0 : ℂ) * 1 + (g 1 : ℂ) * y + (g 2 : ℂ) * z = 0 := hg
  obtain ⟨h0, h1, h2⟩ := h (g 0) (g 1) (g 2) (g 0).2 (g 1).2 (g 2).2
    (by linear_combination hg')
  intro i
  fin_cases i
  · exact Subtype.ext h0
  · exact Subtype.ext h1
  · exact Subtype.ext h2

/-- Part 1. -/
theorem part1
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u v : ℂ}
    (hu : ∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * u + c * conj u = 0 →
      a = 0 ∧ b = 0 ∧ c = 0)
    (hv : ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * v + b * conj v = 0 → a = 0 ∧ b = 0) :
    ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * conj u ∈ LogAlgTilde) := by
  rintro ⟨h0, h1, h2⟩
  -- the conjugates `v̄`, `v̄ ū`, `v̄ u`
  have h3 : conj v ∈ LogAlgTilde := logAlgTilde_conj_stable v h0
  have h4 : conj v * conj u ∈ LogAlgTilde := by
    simpa using logAlgTilde_conj_stable _ h1
  have h5 : conj v * u ∈ LogAlgTilde := by
    simpa using logAlgTilde_conj_stable _ h2
  -- all six products of `x = (v, v̄)` and `y = (1, u, ū)` are in `ℒ̃`
  refine hSSE ![v, conj v] ![1, u, conj u] (linInd_pair hv) (linInd_one_triple hu) ?_
  intro i j
  fin_cases i <;> fin_cases j
  · show v * 1 ∈ LogAlgTilde
    rw [mul_one]; exact h0
  · exact h1
  · exact h2
  · show conj v * 1 ∈ LogAlgTilde
    rw [mul_one]; exact h3
  · exact h5
  · exact h4

/-- Part 2. -/
theorem part2
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u v : ℂ} (hu : u ∉ Qbar) (hv : v ≠ 0) :
    ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * u ^ 2 ∈ LogAlgTilde ∧
      v * u ^ 3 ∈ LogAlgTilde) := by
  rintro ⟨h0, h1, h2, h3⟩
  -- `x = (v, v u)` is free: `a v + b v u = 0` gives `0 u² + b u + a = 0`
  have hx : LinearIndependent (↥Qbar) ![v, v * u] := by
    refine linInd_pair fun a b ha hb hab => ?_
    have hq : (0 : ℂ) * u ^ 2 + b * u + a = 0 := by
      have hvab : v * (a + b * u) = 0 := by linear_combination hab
      linear_combination (mul_eq_zero.1 hvab).resolve_left hv
    obtain ⟨-, hb0, ha0⟩ := quadratic_eq_zero_of_not_mem_Qbar hu Qbar.zero_mem hb ha hq
    exact ⟨ha0, hb0⟩
  -- `y = (1, u, u²)` is free since `u ∉ Q̄`
  have hy : LinearIndependent (↥Qbar) ![1, u, u ^ 2] := by
    refine linInd_one_triple fun a b c ha hb hc habc => ?_
    obtain ⟨hc0, hb0, ha0⟩ := quadratic_eq_zero_of_not_mem_Qbar hu hc hb ha
      (by linear_combination habc)
    exact ⟨ha0, hb0, hc0⟩
  -- the six products are `v, vu, vu², vu, vu², vu³`
  refine hSSE ![v, v * u] ![1, u, u ^ 2] hx hy ?_
  intro i j
  fin_cases i <;> fin_cases j
  · show v * 1 ∈ LogAlgTilde
    rw [mul_one]; exact h0
  · exact h1
  · exact h2
  · show v * u * 1 ∈ LogAlgTilde
    rw [mul_one]; exact h1
  · show v * u * u ∈ LogAlgTilde
    rw [mul_assoc, ← sq]; exact h2
  · show v * u * u ^ 2 ∈ LogAlgTilde
    rw [mul_assoc, ← pow_succ']; exact h3

end Diaz2007Th7

open DiazModulus Diaz2007Th7 in
/-- **Diaz 2007, Théorème 7**, parts 1) and 2) with the "in particular", under Roy's strong six
exponentials theorem `hSSE`. -/
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde)) :
    -- 1)
    (∀ u v : ℂ,
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * u + c * conj u = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      (∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * v + b * conj v = 0 → a = 0 ∧ b = 0) →
      ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * conj u ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ u v : ℂ, u ∉ Qbar → v ≠ 0 →
      ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * u ^ 2 ∈ LogAlgTilde ∧ v * u ^ 3 ∈ LogAlgTilde)) ∧
    (∀ u : ℂ, u ∉ Qbar → ¬ (u ∈ LogAlgTilde ∧ u ^ 2 ∈ LogAlgTilde ∧ u ^ 3 ∈ LogAlgTilde)) := by
  refine ⟨fun u v hu hv => part1 hSSE hu hv, fun u v hu hv => part2 hSSE hu hv, ?_⟩
  -- the "in particular": part 2 with `v = 1`
  rintro u hu ⟨h1, h2, h3⟩
  refine part2 hSSE hu one_ne_zero ⟨one_mem_logAlgTilde, ?_, ?_, ?_⟩
  · rw [one_mul]; exact h1
  · rw [one_mul]; exact h2
  · rw [one_mul]; exact h3
