-- Prove2me | solution 2 for DeBruijnNewman.pf_reflect
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T18:37:37.699845+00:00
-- url     : https://prove2.me/submissions/17eec565-3969-47fb-97c5-8b26127ec9ec

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
    (K : ℝ → ℝ)
    (hK : IsPolyaFrequency K) :
    IsPolyaFrequency (fun x => K (-x)) := by
  intro n x y hx hy
  have h := hK n (fun i => -x (Fin.rev i)) (fun j => -y (Fin.rev j))
    (fun i j hij => neg_lt_neg (hx _ _ (Fin.rev_lt_rev.mpr hij)))
    (fun i j hij => neg_lt_neg (hy _ _ (Fin.rev_lt_rev.mpr hij)))
  have e : (Matrix.of fun i j => K ((fun i => -x (Fin.rev i)) i - (fun j => -y (Fin.rev j)) j))
      = (Matrix.of fun i j => (fun x => K (-x)) (x i - y j)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply]
    congr 1
    ring
  rw [e, Matrix.det_submatrix_equiv_self] at h
  exact h
