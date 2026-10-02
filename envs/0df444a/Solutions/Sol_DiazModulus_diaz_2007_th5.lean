-- Prove2me | solution 1 for DiazModulus.diaz_2007_th5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:45:58.359541+00:00
-- url     : https://prove2.me/submissions/5a63f62a-0543-4879-a5a6-d904f6b21a56

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_diaz_2007_th4

/-!
# Diaz 2007, Théorème 5

G. Diaz, *Produits et quotients de combinaisons linéaires de logarithmes de nombres
algébriques*, JTNB 19 (2007), Théorème 5 (pp. 385–388).

Both parts are Théorème 4 (`DiazModulus.diaz_2007_th4`) with `x = (1, u)` and `y = (v, vu)`.
Then `x₂/x₁ = u`, and the four products are `v, vu, uv = vu, u · vu = vu²`.

* **1)** `(1, u)` is `Q̄`-free because `u ∉ Q̄`: otherwise `u · v - 1 · vu = 0` would be a
  non-trivial relation on `(1, v, vu)`. The triple `(y₁, y₂, 1/x₁)` is `(v, vu, 1)`.
* **2)** `(1, u)` is `ℚ`-free because `u ∉ ℚ`, and `(v, vu)` is `ℚ`-free because `v ≠ 0`:
  `p v + q vu = v (p + q u)`.
-/

open Complex ComplexConjugate

namespace D6_diaz_2007_th5

open DiazModulus

/-- `(1, u)` is `Q̄`-free as soon as `u ∉ Q̄`. -/
theorem one_pair_free_of_not_mem_Qbar {u : ℂ} (hu : u ∉ Qbar) :
    ∀ a b : ℂ, a ∈ Qbar → b ∈ Qbar → a * 1 + b * u = 0 → a = 0 ∧ b = 0 := by
  intro a b ha hb hab
  by_cases hb0 : b = 0
  · subst hb0
    exact ⟨by simpa using hab, rfl⟩
  · refine absurd ?_ hu
    have e : u = -a / b := by
      rw [eq_div_iff hb0]
      linear_combination hab
    rw [e]
    exact Qbar.div_mem (Qbar.neg_mem ha) hb

/-- `(1, u)` is `ℚ`-free as soon as `u ∉ ℚ`. -/
theorem one_pair_free_of_irrational {u : ℂ} (hu : ∀ q : ℚ, u ≠ q) :
    ∀ p q : ℚ, (p : ℂ) * 1 + (q : ℂ) * u = 0 → p = 0 ∧ q = 0 := by
  intro p q hpq
  by_cases hq0 : q = 0
  · subst hq0
    exact ⟨by simpa using hpq, rfl⟩
  · refine absurd ?_ (hu (-p / q))
    have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    push_cast
    rw [eq_div_iff hq0']
    linear_combination hpq

end D6_diaz_2007_th5

open DiazModulus D6_diaz_2007_th5 in
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
    (∀ u v : ℂ, v ≠ 0 →
      (∀ a b c : ℂ, a ∈ Qbar → b ∈ Qbar → c ∈ Qbar → a + b * v + c * (v * u) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) →
      u ∈ LogAlgTilde → ¬ (v ∈ LogAlgTilde ∧ v * u ∈ LogAlgTilde ∧ v * u ^ 2 ∈ LogAlgTilde)) ∧
    -- 2)
    (∀ u v : ℂ, (∀ q : ℚ, u ≠ q) → v ≠ 0 →
      u ∈ LogAlgTilde → ¬ (v ∈ LogAlg ∧ v * u ∈ LogAlg ∧ v * u ^ 2 ∈ LogAlg)) := by
  obtain ⟨th1, th2⟩ := diaz_2007_th4 hSSE hB
  have e : ∀ u v : ℂ, u * (v * u) = v * u ^ 2 := fun u v => by ring
  refine ⟨?_, ?_⟩
  · -- 1) Théorème 4 1) with `x = (1, u)`, `y = (v, vu)`
    intro u v _ hfree hu ⟨h1, h2, h3⟩
    have huQ : u ∉ Qbar := fun hu' =>
      one_ne_zero (neg_eq_zero.1
        (hfree 0 u (-1) Qbar.zero_mem hu' (Qbar.neg_mem Qbar.one_mem) (by ring)).2.2)
    refine th1 1 u v (v * u) (one_pair_free_of_not_mem_Qbar huQ) ?_ (by rwa [div_one])
      ⟨by rwa [one_mul], by rwa [one_mul], by rwa [mul_comm], by rwa [e]⟩
    -- `(v, vu, 1/1)` is `Q̄`-free
    intro a b c ha hb hc habc
    obtain ⟨hc', ha', hb'⟩ := hfree c a b hc ha hb (by linear_combination habc)
    exact ⟨ha', hb', hc'⟩
  · -- 2) Théorème 4 2) with `x = (1, u)`, `y = (v, vu)`
    intro u v hirr hv hu ⟨h1, h2, h3⟩
    have h1u := one_pair_free_of_irrational hirr
    refine th2 1 u v (v * u) h1u ?_ (by rwa [div_one])
      ⟨by rwa [one_mul], by rwa [one_mul], by rwa [mul_comm], by rwa [e]⟩
    -- `(v, vu)` is `ℚ`-free: `p v + q vu = v (p + q u)`
    intro p q hpq
    refine h1u p q ((mul_eq_zero.1 ?_).resolve_left hv)
    linear_combination hpq
