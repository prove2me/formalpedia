-- Prove2me | solution 2 for DeBruijnNewman.pf_dilate_pos
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T18:22:36.470943+00:00
-- url     : https://prove2.me/submissions/dadccd6b-15ea-49c6-8ab6-8a540756d305

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
    (K : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hK : IsPolyaFrequency K) :
    IsPolyaFrequency (fun x => K (c * x)) := by
  intro n x y hx hy
  have h := hK n (fun i => c * x i) (fun j => c * y j)
    (fun i j hij => mul_lt_mul_of_pos_left (hx i j hij) hc)
    (fun i j hij => mul_lt_mul_of_pos_left (hy i j hij) hc)
  simpa [mul_sub] using h
