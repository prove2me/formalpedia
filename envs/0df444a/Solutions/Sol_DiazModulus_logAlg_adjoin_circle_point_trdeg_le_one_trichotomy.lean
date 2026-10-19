-- Prove2me | solution 1 for DiazModulus.logAlg_adjoin_circle_point_trdeg_le_one_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:54:32.641193+00:00
-- url     : https://prove2.me/submissions/576f40af-5424-46e0-9d61-5ed9a36b8612

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_mem_logAlg_adjoin_circle_point_iff
import Theorems.Thm_DiazModulus_logAlg_adjoin_circle_point_trdeg_le_one_logAlg_part_eq_zero
import Theorems.Thm_DiazModulus_logAlg_adjoin_circle_point_trdeg_le_one_hyperbola_case

open Complex ComplexConjugate

/-! # The trichotomy in transcendence degree one (the note's Lemma `lem:trdeg`)

Let `S ⊆ ℒ_u = ℒ + ℚu + ℚū` with `ℚ[S]` of transcendence degree at most one. By
`mem_logAlg_adjoin_circle_point_iff` every `z ∈ S` is `c + p u + q ū` with `c ∈ ℒ`, `p, q ∈ ℚ`;
the same lemma at the point `0` shows that `ℒ` is closed under rational combinations.
(A) If every `z ∈ S` lies in `ℒ`, done. Otherwise fix `z₀ = c₀ + p₀ u + q₀ ū ∈ S` outside `ℒ`, so
`(p₀, q₀) ≠ 0`. (C) If some `z₁ = c₁ + p₁ u + q₁ ū ∈ S` has `D = p₁ q₀ − q₁ p₀ ≠ 0`, then
`(q₀ z₁ − q₁ z₀)/D = c₁′ + u` and `(p₁ z₀ − p₀ z₁)/D = c₂′ + ū` lie in `ℚ[S]` with `c₁′, c₂′ ∈ ℒ`,
and the hyperbola case `logAlg_adjoin_circle_point_trdeg_le_one_hyperbola_case` gives
`S ⊆ ℚu + ℚū`. (B) Otherwise every decomposition `(p, q)` of a `z ∈ S` is parallel to
`(p₀, q₀)`: `(p, q) = r (p₀, q₀)` with `r = (p p₀ + q q₀)/(p₀² + q₀²)`. Then `z − r z₀ ∈ ℒ ∩ ℚ[S]`,
and `logAlg_adjoin_circle_point_trdeg_le_one_logAlg_part_eq_zero` (with the point `z₀`) makes it
`0`: `S` lies on the line `ℚ z₀`. The case split is on the existence of a decomposition with
`D ≠ 0`, so no choice of decompositions is needed. -/

namespace R19_T3
open DiazModulus

/-- `ℒ` is closed under rational combinations: `mem_logAlg_adjoin_circle_point_iff` at `u = 0`. -/
lemma ratComb_mem_logAlg {a b : ℂ} (ha : a ∈ LogAlg) (hb : b ∈ LogAlg) (r s : ℚ) :
    (r : ℂ) * a - (s : ℂ) * b ∈ LogAlg := by
  have hmem : (r : ℂ) * a - (s : ℂ) * b ∈
      (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({(0 : ℂ), conj 0} : Set ℂ)) := by
    apply Submodule.mem_sup_left
    have := Submodule.sub_mem _ (Submodule.smul_mem _ r (Submodule.subset_span ha))
      (Submodule.smul_mem _ s (Submodule.subset_span (R := ℚ) hb))
    rwa [Rat.smul_def, Rat.smul_def] at this
  obtain ⟨c, hc, p, q, h⟩ := ((DiazModulus.mem_logAlg_adjoin_circle_point_iff 0).1 _).1 hmem
  rw [h]
  simpa using hc

/-- A `ℚ`-subalgebra of `ℂ` is stable under rational combinations. -/
lemma ratComb_mem (A : Subalgebra ℚ ℂ) (r s : ℚ) {z w : ℂ} (hz : z ∈ A) (hw : w ∈ A) :
    (r : ℂ) * z - (s : ℂ) * w ∈ A := by
  have h1 := A.smul_mem hz r
  have h2 := A.smul_mem hw s
  rw [Rat.smul_def] at h1 h2
  exact sub_mem h1 h2

/-- Regrouping a rational combination of two decompositions `c + p u + q v`. -/
lemma comb_eq (c₀ c₁ u v : ℂ) (p₀ q₀ p₁ q₁ r s a b : ℚ)
    (h1 : r * p₁ - s * p₀ = a) (h2 : r * q₁ - s * q₀ = b) :
    (r : ℂ) * (c₁ + (p₁ : ℂ) * u + (q₁ : ℂ) * v) - (s : ℂ) * (c₀ + (p₀ : ℂ) * u + (q₀ : ℂ) * v) =
      ((r : ℂ) * c₁ - (s : ℂ) * c₀) + (a : ℂ) * u + (b : ℂ) * v := by
  have h1' : (r : ℂ) * p₁ - s * p₀ = a := by exact_mod_cast h1
  have h2' : (r : ℂ) * q₁ - s * q₀ = b := by exact_mod_cast h2
  linear_combination u * h1' + v * h2'

/-- Coefficients of a combination divided by a non-zero `D`. -/
lemma coeff_div {D r s x y a : ℚ} (hD : D ≠ 0) (h : r * x - s * y = a * D) :
    r / D * x - s / D * y = a := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div, h, mul_div_assoc, div_self hD, mul_one]

end R19_T3

open DiazModulus R19_T3 in
theorem solution
    (u : ℂ) (hρ : IsAlgebraic ℚ (u * conj u))
    (hu : Transcendental (Subfield.closure (LogAlgTilde : Set ℂ)) u)
    (S : Set ℂ) (hS : ∀ z ∈ S, z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ S) ≤ 1) :
    (∀ z ∈ S, z ∈ LogAlg) ∨ (∃ e : ℂ, ∀ z ∈ S, ∃ r : ℚ, z = (r : ℂ) * e) ∨
      (∀ z ∈ S, ∃ p q : ℚ, z = (p : ℂ) * u + (q : ℂ) * conj u) := by
  have hdec : ∀ z ∈ S, ∃ c ∈ LogAlg, ∃ p q : ℚ, z = c + (p : ℂ) * u + (q : ℂ) * conj u :=
    fun z hz => ((DiazModulus.mem_logAlg_adjoin_circle_point_iff u).1 z).1 (hS z hz)
  -- (A) `S ⊆ ℒ`
  by_cases hA : ∀ z ∈ S, z ∈ LogAlg
  · exact Or.inl hA
  simp only [not_forall] at hA
  obtain ⟨z₀, hz₀S, hz₀L⟩ := hA
  obtain ⟨c₀, hc₀, p₀, q₀, hz₀⟩ := hdec z₀ hz₀S
  have hpq₀ : p₀ ≠ 0 ∨ q₀ ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hz₀L
    rw [hz₀, h.1, h.2]
    simpa using hc₀
  have hz₀A : z₀ ∈ Algebra.adjoin ℚ S := Algebra.subset_adjoin hz₀S
  by_cases hC : ∃ z₁ ∈ S, ∃ c₁ ∈ LogAlg, ∃ p₁ q₁ : ℚ,
      z₁ = c₁ + (p₁ : ℂ) * u + (q₁ : ℂ) * conj u ∧ p₁ * q₀ - q₁ * p₀ ≠ 0
  · -- (C) two non-parallel decompositions: the hyperbola case
    right; right
    obtain ⟨z₁, hz₁S, c₁, hc₁, p₁, q₁, hz₁, hD⟩ := hC
    have hz₁A : z₁ ∈ Algebra.adjoin ℚ S := Algebra.subset_adjoin hz₁S
    have e₁ := comb_eq c₀ c₁ u (conj u) p₀ q₀ p₁ q₁ (q₀ / (p₁ * q₀ - q₁ * p₀))
      (q₁ / (p₁ * q₀ - q₁ * p₀)) 1 0 (coeff_div hD (by ring)) (coeff_div hD (by ring))
    have e₂ := comb_eq c₁ c₀ u (conj u) p₁ q₁ p₀ q₀ (p₁ / (p₁ * q₀ - q₁ * p₀))
      (p₀ / (p₁ * q₀ - q₁ * p₀)) 0 1 (coeff_div hD (by ring)) (coeff_div hD (by ring))
    refine DiazModulus.logAlg_adjoin_circle_point_trdeg_le_one_hyperbola_case u hρ hu S hS htr
      (((q₀ / (p₁ * q₀ - q₁ * p₀) : ℚ) : ℂ) * c₁ - ((q₁ / (p₁ * q₀ - q₁ * p₀) : ℚ) : ℂ) * c₀)
      (((p₁ / (p₁ * q₀ - q₁ * p₀) : ℚ) : ℂ) * c₀ - ((p₀ / (p₁ * q₀ - q₁ * p₀) : ℚ) : ℂ) * c₁)
      (ratComb_mem_logAlg hc₁ hc₀ _ _) (ratComb_mem_logAlg hc₀ hc₁ _ _) ?_ ?_
    · have hmem := ratComb_mem _ (q₀ / (p₁ * q₀ - q₁ * p₀)) (q₁ / (p₁ * q₀ - q₁ * p₀)) hz₁A hz₀A
      rw [hz₁, hz₀, e₁] at hmem
      simpa using hmem
    · have hmem := ratComb_mem _ (p₁ / (p₁ * q₀ - q₁ * p₀)) (p₀ / (p₁ * q₀ - q₁ * p₀)) hz₀A hz₁A
      rw [hz₀, hz₁, e₂] at hmem
      simpa using hmem
  · -- (B) all decompositions parallel to `(p₀, q₀)`: `S` lies on the line `ℚ z₀`
    right; left
    refine ⟨z₀, fun z hz => ?_⟩
    obtain ⟨c, hc, p, q, hzc⟩ := hdec z hz
    have hD : p * q₀ - q * p₀ = 0 := by
      by_contra h
      exact hC ⟨z, hz, c, hc, p, q, hzc, h⟩
    have hN : p₀ ^ 2 + q₀ ^ 2 ≠ 0 := by
      rcases hpq₀ with h | h <;> positivity
    obtain ⟨r, hp, hq⟩ : ∃ r : ℚ, r * p₀ = p ∧ r * q₀ = q := by
      refine ⟨(p * p₀ + q * q₀) / (p₀ ^ 2 + q₀ ^ 2), ?_, ?_⟩
      · rw [div_mul_eq_mul_div, div_eq_iff hN]
        linear_combination (-q₀) * hD
      · rw [div_mul_eq_mul_div, div_eq_iff hN]
        linear_combination p₀ * hD
    have e := comb_eq c₀ c u (conj u) p₀ q₀ p q 1 r 0 0 (by linear_combination -hp)
      (by linear_combination -hq)
    have hwA : ((1 : ℚ) : ℂ) * c - (r : ℂ) * c₀ ∈ Algebra.adjoin ℚ S := by
      have hmem := ratComb_mem _ 1 r (Algebra.subset_adjoin hz) hz₀A
      rw [hzc, hz₀, e] at hmem
      simpa using hmem
    have h0 := DiazModulus.logAlg_adjoin_circle_point_trdeg_le_one_logAlg_part_eq_zero u hρ hu S
      htr c₀ p₀ q₀ hc₀ hpq₀ (hz₀ ▸ hz₀A) _ (ratComb_mem_logAlg hc hc₀ 1 r) hwA
    have hp' : (r : ℂ) * p₀ = p := by exact_mod_cast hp
    have hq' : (r : ℂ) * q₀ = q := by exact_mod_cast hq
    push_cast at h0
    refine ⟨r, ?_⟩
    rw [hzc, hz₀]
    linear_combination h0 - u * hp' - conj u * hq'
