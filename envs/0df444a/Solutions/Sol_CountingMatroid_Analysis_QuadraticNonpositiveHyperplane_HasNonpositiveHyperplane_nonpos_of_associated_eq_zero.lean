-- Prove2me | solution 1 for CountingMatroid.Analysis.QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane.nonpos_of_associated_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:43:46.041655+00:00
-- url     : https://prove2.me/submissions/32543d6a-1162-429c-8726-c7b72ad2fe91

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

set_option autoImplicit false

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane
end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

/-- INTERNAL: A nonpositive hyperplane forces nonpositivity on the associated
orthogonal complement of every positive vector. This identifies the exact
kernel used in the parent proof without choosing a special hyperplane.
TEXLINE: main.tex:326-348 -/
theorem solution {V : Type}
    [AddCommGroup V] [Module ℝ V] [Invertible (2 : ℝ)]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q)
    (e v : V) (he : 0 < Q e) (hv : Q.associated e v = 0) : Q v ≤ 0 := by
  obtain ⟨l, hl⟩ := hQ
  have hle : l e ≠ 0 := by
    intro h
    exact (not_le_of_gt he) (hl e h)
  have hu := hl ((l e) • v - (l v) • e) (by simp [mul_comm])
  have hpolar : QuadraticMap.polar Q v e = 0 := by
    have horth := (QuadraticMap.associated_isOrtho.mp hv).symm
    exact horth.polar_eq_zero
  have hexp : Q ((l e) • v - (l v) • e) =
      (l e) ^ 2 * Q v + (l v) ^ 2 * Q e := by
    rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q ((l e) • v) (-(l v) • e),
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpolar]
    simp only [QuadraticMap.map_smul, smul_eq_mul]
    ring
  rw [hexp] at hu
  have hterm : 0 ≤ (l v) ^ 2 * Q e := mul_nonneg (sq_nonneg _) he.le
  have hsq : 0 < (l e) ^ 2 := sq_pos_of_ne_zero hle
  nlinarith
