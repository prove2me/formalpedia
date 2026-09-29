-- Prove2me | solution 1 for ChanPangGQVI.Existence.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:40:10.499445+00:00
-- url     : https://prove2.me/submissions/ca85f452-ce31-4c88-8127-d185ab2b7ec1

import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_GICP

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

theorem prop21_core {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      IsGICPSolution L m f x y ↔ IsGQVISolution (coneTranslate m L) f x y := by
  intro x y
  constructor
  · rintro ⟨hx, hy, hd, h0⟩
    refine ⟨hx, hy, ?_⟩
    rintro x' ⟨z, hz, rfl⟩
    have h1 := hd z hz
    have : m x + z - x = z - (x - m x) := by abel
    rw [this, inner_sub_left]
    have c1 := real_inner_comm z y
    have c2 := real_inner_comm (x - m x) y
    linarith
  · rintro ⟨hx, hy, hv⟩
    refine ⟨hx, hy, ?_, ?_⟩
    · obtain ⟨z0, hz0, hxe⟩ := hx
      intro z hz
      have := hv (m x + (z0 + z)) ⟨z0 + z, L x |>.add_mem hz0 hz, rfl⟩
      have e3 : x - m x = z0 := sub_eq_iff_eq_add'.mpr hxe
      have e : m x + (z0 + z) - x = z := by
        rw [← e3]; abel
      rw [e, real_inner_comm] at this
      exact this
    · obtain ⟨z0, hz0, hxe⟩ := hx
      have h1 := hv (m x + 0) ⟨0, (L x).zero_mem, rfl⟩
      have h2 := hv (m x + (2:ℝ) • z0) ⟨(2:ℝ) • z0, (L x).smul_mem (by norm_num : (0:ℝ) ≤ 2) hz0, rfl⟩
      have e3 : x - m x = z0 := sub_eq_iff_eq_add'.mpr hxe
      have e1 : m x + 0 - x = -z0 := by rw [← e3]; abel
      have e2 : m x + (2:ℝ) • z0 - x = z0 := by rw [← e3, two_smul]; abel
      rw [e1, inner_neg_left] at h1
      rw [e2] at h2
      rw [e3, real_inner_comm]
      linarith

end ChanPangGQVI.Existence

open ChanPangGQVI.Existence
open scoped RealInnerProductSpace

theorem solution {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      IsGICPSolution L m f x y ↔ IsGQVISolution (coneTranslate m L) f x y := by
  exact prop21_core L m f
