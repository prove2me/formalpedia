-- Prove2me | solution 1 for DiazModulus.laurent_involution_class_space_cyclic_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T11:55:59.237759+00:00
-- url     : https://prove2.me/submissions/ea8d2797-0473-40df-93a6-371a270f4c9b

import Mathlib
import Definitions.Def_DiazModulus

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Complex ComplexConjugate

/-! # The involution class is a cyclic (D2b) span with an explicit pencil

Write `v = u/s`. Since `s² = uū = |u|² > 0`, `s` is real, so `v̄ = s/u` and `ū = s²/u`.
Take the coprime pencil `P′ = sX`, `Q′ = X² + βs²` (Bézout: `−(sβs²)⁻¹X·P′ + (βs²)⁻¹Q′ = 1`),
with `S₁ = s/β + (e/s)X²` and `S₂ = (ζ/s)X²`. With `n₀ = v̄² + ev²`, `n₁ = βv̄³ + ζv² + ev³` and
`g₁ = Q′S₁/(uP′)`, `g₂ = Q′(Q′S₁ + P′S₂)/(uP′²)` (all evaluated at `u`), two exact identities hold:
`g₁ − n₀ = βe + β⁻¹` and `g₂ − n₁ = βζ + ((2βe + β⁻¹)/s)·u + ((β²e + 2)/s)·ū`.
Both residues lie in `H₀ = span(1, u, ū) = span(1, u, u⁻¹)` (as `ū = s²·u⁻¹`), so each generator of
`span(1, u, ū, n₀, n₁)` is an explicit `Q̄`-combination of `1, u, u⁻¹, g₁, g₂` and conversely.
This gives the equality of spans by two inclusions; no dimension or independence argument is needed,
and the identity holds for all `e, β, ζ ∈ Q̄` with `β ≠ 0`. The degree conditions are direct.
-/

namespace R21a_B2

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem span_mul_mem {S : Set ℂ} {c w : ℂ} (hc : c ∈ Qbar) (hw : w ∈ Submodule.span Qbar S) :
    c * w ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hw
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- An explicit `Q̄`-combination of five generators lies in their span. -/
theorem mem5 {v t z zc x x₀ x₁ x₂ x₃ x₄ : ℂ} (h₀ : x₀ ∈ Qbar) (h₁ : x₁ ∈ Qbar) (h₂ : x₂ ∈ Qbar)
    (h₃ : x₃ ∈ Qbar) (h₄ : x₄ ∈ Qbar) (hx : x = x₀ + x₁ * v + x₂ * t + x₃ * z + x₄ * zc) :
    x ∈ Submodule.span Qbar ({1, v, t, z, zc} : Set ℂ) := by
  have g : ∀ {c : ℂ} (w : ℂ), c ∈ Qbar → w ∈ ({1, v, t, z, zc} : Set ℂ) →
      c * w ∈ Submodule.span Qbar ({1, v, t, z, zc} : Set ℂ) :=
    fun _ hc hw => span_mul_mem hc (Submodule.subset_span hw)
  have := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (g 1 h₀ (by simp)) (g v h₁ (by simp))) (g t h₂ (by simp))) (g z h₃ (by simp)))
    (g zc h₄ (by simp))
  rwa [mul_one, ← hx] at this

/-- A five-generator span lies in a submodule containing the five generators. -/
theorem span5_le {a b c d e : ℂ} {W : Submodule (↥Qbar) ℂ} (ha : a ∈ W) (hb : b ∈ W)
    (hc : c ∈ W) (hd : d ∈ W) (he : e ∈ W) :
    Submodule.span Qbar ({a, b, c, d, e} : Set ℂ) ≤ W := by
  rw [Submodule.span_le]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- `s² = uū` with `u ≠ 0` forces `s` to be real. -/
theorem conj_s {u s : ℂ} (hu0 : u ≠ 0) (hss : s * s = u * conj u) : conj s = s := by
  rw [Complex.conj_eq_iff_im]
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.2 hu0
  rw [Complex.mul_conj] at hss
  have hre := congrArg Complex.re hss
  have him := congrArg Complex.im hss
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  have : s.re * s.im = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · rw [h] at hre; nlinarith
  · exact h

end R21a_B2

open DiazModulus R21a_B2 in
open Polynomial in
theorem solution (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (e β ζ : ℂ) (he : e ∈ Qbar) (hβ : β ∈ Qbar) (hζ : ζ ∈ Qbar) (hβ0 : β ≠ 0) :
    ∃ P' Q' S₁ S₂ : (↥Qbar)[X], aeval u P' = s * u ∧ aeval u Q' = u ^ 2 + β * s ^ 2 ∧
      aeval u S₁ = s / β + e / s * u ^ 2 ∧ aeval u S₂ = ζ / s * u ^ 2 ∧
      IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧ S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
      Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ) =
        Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} : Set ℂ) := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h0 : u * conj u = 0 := by rw [← hss]; ring
    rcases mul_eq_zero.1 h0 with h | h
    · exact hu0 h
    · exact hu0 (by simpa using h)
  have hcs : conj s = s := conj_s hu0 hss
  have hcu : conj u = s * s / u := by field_simp; linear_combination -hss
  have hcv : conj (u / s) = s / u := by
    rw [map_div₀, hcs, hcu]; field_simp
  set s' : ↥Qbar := ⟨s, hs⟩
  set b' : ↥Qbar := ⟨β, hβ⟩
  set e' : ↥Qbar := ⟨e, he⟩
  set z' : ↥Qbar := ⟨ζ, hζ⟩
  have hs'0 : s' ≠ 0 := fun h => hs0 (congrArg Subtype.val h)
  have hb'0 : b' ≠ 0 := fun h => hβ0 (congrArg Subtype.val h)
  have hc0 : b' * s' ^ 2 ≠ 0 := mul_ne_zero hb'0 (pow_ne_zero 2 hs'0)
  have hP : aeval u (C s' * X) = s * u := by simp only [map_mul, aeval_C, aeval_X, am]; rfl
  have hQ : aeval u (X ^ 2 + C (b' * s' ^ 2)) = u ^ 2 + β * s ^ 2 := by
    simp only [map_add, map_pow, aeval_C, aeval_X, am]; rfl
  have hS1 : aeval u (C (s' / b') + C (e' / s') * X ^ 2) = s / β + e / s * u ^ 2 := by
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; rfl
  have hS2 : aeval u (C (z' / s') * X ^ 2) = ζ / s * u ^ 2 := by
    simp only [map_mul, map_pow, aeval_C, aeval_X, am]; rfl
  have hcop : IsCoprime (C s' * X) (X ^ 2 + C (b' * s' ^ 2)) := by
    refine ⟨-C (s'⁻¹ * (b' * s' ^ 2)⁻¹) * X, C (b' * s' ^ 2)⁻¹, ?_⟩
    have h1 : s'⁻¹ * (b' * s' ^ 2)⁻¹ * s' = (b' * s' ^ 2)⁻¹ := by field_simp
    have h2 : (b' * s' ^ 2)⁻¹ * (b' * s' ^ 2) = 1 := inv_mul_cancel₀ hc0
    calc _ = -C (s'⁻¹ * (b' * s' ^ 2)⁻¹ * s') * X ^ 2 + C (b' * s' ^ 2)⁻¹ * X ^ 2 +
          C ((b' * s' ^ 2)⁻¹ * (b' * s' ^ 2)) := by simp only [map_mul]; ring
      _ = 1 := by rw [h1, h2, C_1]; ring
  have hdeg : max (C s' * X).natDegree (X ^ 2 + C (b' * s' ^ 2)).natDegree = 2 := by
    rw [natDegree_X_pow_add_C]
    have : (C s' * X).natDegree ≤ 1 := by compute_degree
    omega
  refine ⟨_, _, _, _, hP, hQ, hS1, hS2, hcop, hdeg, by compute_degree, by compute_degree, ?_⟩
  rw [hP, hQ, hS1, hS2, hcv, hcu]
  have h2 : (2 : ℂ) ∈ Qbar := by norm_num
  apply le_antisymm
  · apply span5_le
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · refine mem5 (x₀ := 0) (x₁ := 0) (x₂ := s * s) (x₃ := 0) (x₄ := 0) ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try (repeat' (first
          | assumption | exact zero_mem _ | exact one_mem _ | apply div_mem | apply inv_mem
          | apply neg_mem | apply pow_mem | apply sub_mem | apply add_mem | apply mul_mem))
      field_simp <;> ring
    · refine mem5 (x₀ := -(β * e + β⁻¹)) (x₁ := 0) (x₂ := 0) (x₃ := 1) (x₄ := 0)
        ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try (repeat' (first
          | assumption | exact zero_mem _ | exact one_mem _ | apply div_mem | apply inv_mem
          | apply neg_mem | apply pow_mem | apply sub_mem | apply add_mem | apply mul_mem))
      field_simp <;> ring
    · refine mem5 (x₀ := -(β * ζ)) (x₁ := -((2 * β * e + β⁻¹) / s))
        (x₂ := -(s * (β ^ 2 * e + 2))) (x₃ := 0) (x₄ := 1) ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try (repeat' (first
          | assumption | exact zero_mem _ | exact one_mem _ | apply div_mem | apply inv_mem
          | apply neg_mem | apply pow_mem | apply sub_mem | apply add_mem | apply mul_mem))
      field_simp <;> ring
  · apply span5_le
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · refine mem5 (x₀ := 0) (x₁ := 0) (x₂ := 1 / (s * s)) (x₃ := 0) (x₄ := 0)
        ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try (repeat' (first
          | assumption | exact zero_mem _ | exact one_mem _ | apply div_mem | apply inv_mem
          | apply neg_mem | apply pow_mem | apply sub_mem | apply add_mem | apply mul_mem))
      field_simp <;> ring
    · refine mem5 (x₀ := β * e + β⁻¹) (x₁ := 0) (x₂ := 0) (x₃ := 1) (x₄ := 0)
        ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try (repeat' (first
          | assumption | exact zero_mem _ | exact one_mem _ | apply div_mem | apply inv_mem
          | apply neg_mem | apply pow_mem | apply sub_mem | apply add_mem | apply mul_mem))
      field_simp <;> ring
    · refine mem5 (x₀ := β * ζ) (x₁ := (2 * β * e + β⁻¹) / s)
        (x₂ := (β ^ 2 * e + 2) / s) (x₃ := 0) (x₄ := 1) ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try (repeat' (first
          | assumption | exact zero_mem _ | exact one_mem _ | apply div_mem | apply inv_mem
          | apply neg_mem | apply pow_mem | apply sub_mem | apply add_mem | apply mul_mem))
      field_simp <;> ring
