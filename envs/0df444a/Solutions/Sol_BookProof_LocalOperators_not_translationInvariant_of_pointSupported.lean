-- Prove2me | solution 1 for BookProof.LocalOperators.not_translationInvariant_of_pointSupported
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:39:31.735777+00:00
-- url     : https://prove2.me/submissions/ef0bb9f5-c547-43ea-a1eb-747c87237a8c

-- Generated from ChapterLocalOperators.lean — solution of BookProof.LocalOperators.not_translationInvariant_of_pointSupported
import Mathlib
import Definitions.Def_ChapterLocalOperators
open BookProof.LocalOperators




open MeasureTheory

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution
    (hd : 0 < d) (l : LocalField d E) (x₀ : Fin d → ℝ)
    (hne : l x₀ ≠ 0) (hsupp : ∀ z, z ≠ x₀ → l z = 0) :
    ¬ TranslationInvariant l := by

  intro h
  set i : Fin d := ⟨0, hd⟩
  set y : Fin d → ℝ := fun j => if j = i then 1 else 0 with hy
  have hy0 : y ≠ 0 := by
    intro hcon
    have := congrFun hcon i
    simp [hy] at this
  have hx : x₀ + y ≠ x₀ := by
    intro hcon
    apply hy0
    have : y = (x₀ + y) - x₀ := by ring
    rw [this, hcon]; ring
  have h2 : l (x₀ + y) = l x₀ := congrFun (h y) x₀
  rw [hsupp _ hx] at h2
  exact hne h2.symm
