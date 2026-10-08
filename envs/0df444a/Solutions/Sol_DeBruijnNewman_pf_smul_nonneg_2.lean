-- Prove2me | solution 2 for DeBruijnNewman.pf_smul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T18:52:38.64954+00:00
-- url     : https://prove2.me/submissions/98129751-80ae-45b6-9bd0-472f065dbe02

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
    (K : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hK : IsPolyaFrequency K) :
    IsPolyaFrequency (fun x => a * K x) := by
  intro n x y hx hy
  have hM : (Matrix.of fun i j => (fun x => a * K x) (x i - y j))
      = a • (Matrix.of fun i j => K (x i - y j)) := by
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul]
  rw [hM, Matrix.det_smul]
  exact mul_nonneg (pow_nonneg ha _) (hK n x y hx hy)
