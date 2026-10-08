-- Prove2me | solution 1 for Erdos3.erdos_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:24:41.963407+00:00
-- url     : https://prove2.me/submissions/6173b4b4-6384-4f07-950d-6700fca456b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos142Basic
import Theorems.Thm_OAI_Erdos3_manuscriptReciprocalProgressionTheorem

/-! Bridge from OpenAI's `OAI.Erdos3.ReciprocalProgressionTheorem` to prove2.me's
`Erdos3.erdos_3` (goal a1db8c60 of mission 96efaf70). -/

namespace OAIErdos3Bridge

open Erdos142

/-- A progression `a, a + d, …, a + (k-1)d` with `d > 0` inside `A` gives a set `S ⊆ A` with
`IsAPOfLength S k`. -/
theorem exists_isAPOfLength_of_hasAP {A : Set ℕ} {k : ℕ} (h : OAI.Erdos3.HasAP A k) :
    ∃ S ⊆ A, IsAPOfLength S (k : ℕ∞) := by
  obtain ⟨a, d, hd, hA⟩ := h
  refine ⟨(fun n : ℕ ↦ a + n * d) '' Set.Iio k, ?_, a, d, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact hA n hn
  · have hinj : Function.Injective (fun n : ℕ ↦ a + n * d) := by
      intro m n hmn
      have : m * d = n * d := by simpa using hmn
      exact Nat.eq_of_mul_eq_mul_right hd this
    rw [ENat.card_image_of_injective _ _ hinj]
    simp
  · ext x
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_ofPred_eq, smul_eq_mul, Nat.cast_lt]
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩

/-- The two non-summability hypotheses agree: the platform sums `1 / a` over the subtype `A`,
OpenAI sums the indicator `reciprocalTerm A` over `ℕ`. -/
theorem not_summable_reciprocalTerm {A : Set ℕ}
    (h : ¬ Summable fun a : A ↦ 1 / (a : ℝ)) : ¬ Summable (OAI.Erdos3.reciprocalTerm A) := by
  intro hs
  apply h
  have heq : OAI.Erdos3.reciprocalTerm A = A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) := by
    funext n
    classical
    simp only [OAI.Erdos3.reciprocalTerm, Set.indicator, one_div]
  rw [heq, ← summable_subtype_iff_indicator] at hs
  exact hs

theorem erdos_3_of_oai (H : OAI.Erdos3.ReciprocalProgressionTheorem) : ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, IsAPOfLength S k := by
  intro A hA
  exact Filter.Frequently.of_forall fun k ↦
    exists_isAPOfLength_of_hasAP (H A (not_summable_reciprocalTerm hA) k)

end OAIErdos3Bridge

open Erdos142 in
theorem solution : ∀ A : Set ℕ,
    (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, IsAPOfLength S k :=
  OAIErdos3Bridge.erdos_3_of_oai OAI.Erdos3.manuscriptReciprocalProgressionTheorem
