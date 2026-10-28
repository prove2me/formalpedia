-- Prove2me | solution 1 for CelestialWedge.soft_mode_rescaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:39:01.420075+00:00
-- url     : https://prove2.me/submissions/4da23b76-24c9-4955-990b-b17a301a74bc

import Mathlib
import Definitions.Def_celestial_wedge_algebra
open CelestialWedge

theorem solution {V : Type*} [AddCommGroup V] [Module ℂ V]
    (br : V →ₗ[ℂ] V →ₗ[ℂ] V) (κ : ℂ) (hκ : κ ≠ 0) (H : ℚ → ℚ → V)
    (hH : ∀ k l m n : ℚ, InSoftRange k m → InSoftRange l n →
      br (H k m) (H l n) = softCoeff κ k l m n • H (k + l) (m + n))
    (p m q n : ℚ) (hpm : InWedge p m) (hqn : InWedge q n) :
    br (rescale κ H p m) (rescale κ H q n) =
      ((structConst p m q n : ℚ) : ℂ) • rescale κ H (p + q - 2) (m + n) := by
  have h1 : InSoftRange (-2*p+4) m := by
    unfold InSoftRange; convert hpm using 1; ring
  have h2 : InSoftRange (-2*q+4) n := by
    unfold InSoftRange; convert hqn using 1; ring
  have key := hH _ _ _ _ h1 h2
  rw [rescale, rescale, rescale, map_smul, map_smul, LinearMap.smul_apply, key]
  simp only [smul_smul]
  rw [show -2*p+4 + (-2*q+4) = -2*(p+q-2)+4 by ring]
  congr 1
  unfold softCoeff structConst
  rw [show (2 - (-2*p+4))/2 - m = p - m - 1 by ring, show (2 - (-2*q+4))/2 - n = q - n - 1 by ring,
    show (2 - (-2*p+4))/2 + m = p + m - 1 by ring, show (2 - (-2*q+4))/2 + n = q + n - 1 by ring,
    show p - m - 1 + (q - n - 1) - 1 = p + q - 2 - (m + n) - 1 by ring,
    show p + m - 1 + (q + n - 1) - 1 = p + q - 2 + (m + n) - 1 by ring]
  have f1 := Nat.factorial_ne_zero ⌊p - m - 1⌋₊
  have f2 := Nat.factorial_ne_zero ⌊q - n - 1⌋₊
  have f3 := Nat.factorial_ne_zero ⌊p + m - 1⌋₊
  have f4 := Nat.factorial_ne_zero ⌊q + n - 1⌋₊
  push_cast
  field_simp
  ring
