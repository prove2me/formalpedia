-- Prove2me | solution 1 for DeBruijnNewman.pf_translate
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T19:07:48.573345+00:00
-- url     : https://prove2.me/submissions/08b9e8b3-8794-4c38-99cb-76a3291b23f8

import Mathlib

/-- A function `K : ℝ → ℝ` is a Pólya frequency function if the translation
kernel `(x, y) ↦ K (x - y)` is totally positive of every order: every
finite minor formed on strictly increasing nodes is nonnegative. -/
def IsPolyaFrequency (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℝ),
    (∀ i j : Fin n, i < j → x i < x j) →
    (∀ i j : Fin n, i < j → y i < y j) →
    0 ≤ (Matrix.of fun i j => K (x i - y j)).det


theorem solution
    (K : ℝ → ℝ) (c : ℝ)
    (hK : IsPolyaFrequency K) :
    IsPolyaFrequency (fun x => K (x - c)) := by
  intro n x y hx hy
  have h := hK n x (fun j => y j + c) hx
    (fun i j hij => by simp only [add_lt_add_iff_right]; exact hy i j hij)
  refine le_of_le_of_eq h ?_
  congr 1
  ext i j
  simp [Matrix.of_apply, sub_sub]
