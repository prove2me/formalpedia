-- Prove2me | solution 1 for DiazModulus.four_pow_hull_no_two_by_three
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:36:15.104889+00:00
-- url     : https://prove2.me/submissions/3bd558fe-dce5-44cc-9971-6f0835cbf5eb

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_hull_config_iff
import Theorems.Thm_DiazModulus_two_sumset_iff_difference_count

open Complex ComplexConjugate

/-! # No `2 × 3` configuration in `Σ_{s ∈ T} K uˢ`, `T = {0, ±1} ∪ {±4ʲ : j ≥ 1}`

The six products lie in the span of finitely many powers `uˢ`, `s` in a finite `S' ⊆ T`. By
`laurent_hull_config_iff`, `S'` contains a sumset `A + B` with `|A| = 2`, `|B| = 3`, and by
`two_sumset_iff_difference_count` some `d > 0` has three `s ∈ S'` with `s + d ∈ S'`.

This is impossible in `T`. The absolute values in `T` are `0` and powers of `4`, so two of them
are equal or differ by a factor at least `4`. For a pair `s < t = s + d` in `T` let `M` be the
larger of `|s|, |t|`: either `s = −M`, `t = M`, `d = 2M`, or `|d − M| ≤ M/4` and
`s ∈ {M − d, −M}`. The factor `4` gap then forces the same `M` and the same case for every pair
with difference `d`, so `s` takes at most two values.
-/

namespace R6_fourpow

open DiazModulus

/-- The exponent set. -/
def T : Set ℤ := {s : ℤ | s = 0 ∨ s = 1 ∨ s = -1 ∨ ∃ j : ℕ, 1 ≤ j ∧ (s = 4 ^ j ∨ s = -4 ^ j)}

theorem neg_mem {x : ℤ} (hx : x ∈ T) : -x ∈ T := by
  rcases hx with rfl | rfl | rfl | ⟨j, hj, rfl | rfl⟩
  · exact Or.inl neg_zero
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl (neg_neg 1))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hj, Or.inr rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, hj, Or.inl (neg_neg _)⟩))

theorem four_le_pow {j : ℕ} (hj : 1 ≤ j) : (4 : ℤ) ≤ 4 ^ j := by
  simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) hj

/-- Two non-negative elements of `T`: equal, or a factor at least `4` apart. -/
theorem sep {x y : ℤ} (hx : x ∈ T) (hy : y ∈ T) (h0 : 0 ≤ x) (hxy : x < y) : 4 * x ≤ y := by
  rcases hy with rfl | rfl | rfl | ⟨i, hi, rfl | rfl⟩
  · omega
  · rcases hx with rfl | rfl | rfl | ⟨j, hj, rfl | rfl⟩ <;> omega
  · omega
  · have hi4 := four_le_pow hi
    rcases hx with rfl | rfl | rfl | ⟨j, hj, rfl | rfl⟩ <;> try omega
    · have hji : j < i := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 4)).1 hxy
      calc 4 * 4 ^ j = (4 : ℤ) ^ (j + 1) := by ring
        _ ≤ 4 ^ i := pow_le_pow_right₀ (by norm_num) hji
    · have := four_le_pow hj; omega
  · have := four_le_pow hi; omega

theorem abs_mem {x : ℤ} (hx : x ∈ T) : ∃ a ∈ T, 0 ≤ a ∧ (x = a ∨ x = -a) := by
  rcases le_or_gt 0 x with h | h
  · exact ⟨x, hx, h, Or.inl rfl⟩
  · exact ⟨-x, neg_mem hx, by omega, Or.inr (neg_neg x).symm⟩

/-- The shape of a pair `s < s + d` in `T`, with `M = max (|s|, |s + d|)`. -/
theorem shape {s d : ℤ} (hs : s ∈ T) (ht : s + d ∈ T) (hd : 0 < d) :
    ∃ M ∈ T, 0 < M ∧ ((d = 2 * M ∧ s = -M) ∨
      (3 * M ≤ 4 * d ∧ 4 * d ≤ 5 * M ∧ (s = M - d ∨ s = -M))) := by
  obtain ⟨a, ha, ha0, has⟩ := abs_mem hs
  obtain ⟨b, hb, hb0, hbt⟩ := abs_mem ht
  rcases lt_trichotomy a b with h | rfl | h
  · have := sep ha hb ha0 h
    exact ⟨b, hb, by omega, by omega⟩
  · exact ⟨a, ha, by omega, by omega⟩
  · have := sep hb ha hb0 h
    exact ⟨a, ha, by omega, by omega⟩

/-- In `T`, no difference `d > 0` occurs three times. -/
theorem comb {d s₁ s₂ s₃ : ℤ} (hd : 0 < d) (h₁ : s₁ ∈ T) (h₁' : s₁ + d ∈ T) (h₂ : s₂ ∈ T)
    (h₂' : s₂ + d ∈ T) (h₃ : s₃ ∈ T) (h₃' : s₃ + d ∈ T) (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ s₃)
    (h23 : s₂ ≠ s₃) : False := by
  obtain ⟨M₁, hM₁, hM₁0, e₁⟩ := shape h₁ h₁' hd
  obtain ⟨M₂, hM₂, hM₂0, e₂⟩ := shape h₂ h₂' hd
  obtain ⟨M₃, hM₃, hM₃0, e₃⟩ := shape h₃ h₃' hd
  have a12 : M₁ < M₂ → 4 * M₁ ≤ M₂ := sep hM₁ hM₂ hM₁0.le
  have a21 : M₂ < M₁ → 4 * M₂ ≤ M₁ := sep hM₂ hM₁ hM₂0.le
  have a13 : M₁ < M₃ → 4 * M₁ ≤ M₃ := sep hM₁ hM₃ hM₁0.le
  have a31 : M₃ < M₁ → 4 * M₃ ≤ M₁ := sep hM₃ hM₁ hM₃0.le
  have a23 : M₂ < M₃ → 4 * M₂ ≤ M₃ := sep hM₂ hM₃ hM₂0.le
  have a32 : M₃ < M₂ → 4 * M₃ ≤ M₂ := sep hM₃ hM₂ hM₃0.le
  omega

/-- An element of a span of powers lies in the span of finitely many of them. -/
theorem exists_finset {K : Subfield ℂ} {f : ℤ → ℂ} {S : Set ℤ} {v : ℂ}
    (hv : v ∈ Submodule.span K (f '' S)) :
    ∃ F : Finset ℤ, ↑F ⊆ S ∧ v ∈ Submodule.span K (f '' ↑F) := by
  obtain ⟨l, hl, rfl⟩ := Finsupp.mem_span_image_iff_linearCombination K |>.1 hv
  exact ⟨l.support, hl, Finsupp.mem_span_image_iff_linearCombination K |>.2 ⟨l, fun _ h => h, rfl⟩⟩

end R6_fourpow

open DiazModulus R6_fourpow in
theorem solution (K : Subfield ℂ) (u : ℂ) (hT : Transcendental K u) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent K x ∧ LinearIndependent K y ∧
      ∀ i j, x i * y j ∈ Submodule.span K ((fun s : ℤ => u ^ s) ''
        {s : ℤ | s = 0 ∨ s = 1 ∨ s = -1 ∨ ∃ j : ℕ, 1 ≤ j ∧ (s = 4 ^ j ∨ s = -4 ^ j)}) := by
  rintro ⟨x, y, hx, hy, hxy⟩
  choose F hFT hF using fun i j => exists_finset (hxy i j)
  let S' : Finset ℤ := Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => F i j
  have hS'T : ∀ s ∈ S', s ∈ T := by
    intro s hs
    simp only [S', Finset.mem_biUnion, Finset.mem_univ, true_and] at hs
    obtain ⟨i, j, h⟩ := hs
    exact hFT i j h
  have hmem : ∀ i j, x i * y j ∈ Submodule.span K ((fun s : ℤ => u ^ s) '' (S' : Set ℤ)) :=
    fun i j => Submodule.span_mono (Set.image_mono fun s hs => by
      simp only [S', Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Set.mem_iUnion]
      exact ⟨i, j, hs⟩) (hF i j)
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    (DiazModulus.laurent_hull_config_iff K u hT S' 2 3 (by norm_num) (by norm_num)).1
      ⟨x, y, hx, hy, hmem⟩
  obtain ⟨d, hd, hcard⟩ := (DiazModulus.two_sumset_iff_difference_count S' 3).1 ⟨A, B, hA, hB, hAB⟩
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := (Finset.two_lt_card (s := S'.filter fun s => s + d ∈ S')).1 (by omega)
  rw [Finset.mem_filter] at ha hb hc
  exact comb hd (hS'T _ ha.1) (hS'T _ ha.2) (hS'T _ hb.1) (hS'T _ hb.2) (hS'T _ hc.1)
    (hS'T _ hc.2) hab hac hbc
