-- Prove2me | solution 1 for CurveSymmetry.direct_symmetries_common_center
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:13.459592+00:00
-- url     : https://prove2.me/submissions/f261f58a-08d0-4e3a-a51c-8ff4cec95600

-- Solution generated from lean/EuclideanCenter.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Theorems.Thm_CurveSymmetry_no_translation_symmetry
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
lemma direct_coeff_ne_zero {S : Set ℂ} {a b : ℂ} (h : DirectSymmetry S a b) : a ≠ 0 := by
  intro hz
  have hnorm := h.1
  simp [hz] at hnorm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
/-- The two affine compositions differ by a translation, so must agree. -/
lemma direct_symmetries_commute {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty)
    {a b c d : ℂ} (h1 : DirectSymmetry (realLocus P) a b)
    (h2 : DirectSymmetry (realLocus P) c d) : a * d + b = c * b + d := by
  have hk : a * c ≠ 0 := mul_ne_zero (direct_coeff_ne_zero h1) (direct_coeff_ne_zero h2)
  have hc1 : ∀ z : ℂ, a * c * z + (a * d + b) ∈ realLocus P ↔ z ∈ realLocus P := by
    intro z
    rw [show a * c * z + (a * d + b) = a * (c * z + d) + b by ring]
    exact (h1.2 (c * z + d)).trans (h2.2 z)
  have hc2 : ∀ z : ℂ, a * c * z + (c * b + d) ∈ realLocus P ↔ z ∈ realLocus P := by
    intro z
    rw [show a * c * z + (c * b + d) = c * (a * z + b) + d by ring]
    exact (h2.2 (a * z + b)).trans (h1.2 z)
  have ht : ∀ z ∈ realLocus P, z + ((a * d + b) - (c * b + d)) ∈ realLocus P := by
    intro z hz
    let w := (z - (c * b + d)) / (a * c)
    have he : a * c * w + (c * b + d) = z := by
      dsimp [w]
      rw [mul_div_cancel₀ _ hk]
      ring
    have hw : w ∈ realLocus P := (hc2 w).mp (he ▸ hz)
    have hout := (hc1 w).mpr hw
    have he' : a * c * w + (a * d + b) = z + ((a * d + b) - (c * b + d)) := by
      linear_combination he
    rwa [he'] at hout
  exact sub_eq_zero.mp (no_translation_symmetry hP hd hne ht)
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) :
    ∃ z : ℂ, ∀ a b : ℂ, DirectSymmetry (realLocus P) a b → b = (1 - a) * z := by
  by_cases hex : ∃ a b : ℂ, DirectSymmetry (realLocus P) a b ∧ a ≠ 1
  · obtain ⟨a, b, hab, ha⟩ := hex
    refine ⟨b / (1 - a), ?_⟩
    intro c d hcd
    have h := direct_symmetries_commute hP hd hne hab hcd
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
    field_simp
    linear_combination -h
  · refine ⟨0, ?_⟩
    intro a b hab
    have ha : a = 1 := by by_contra h; exact hex ⟨a, b, hab, h⟩
    have hb : b = 0 := no_translation_symmetry hP hd hne (by
      intro z hz
      simpa [ha] using (hab.2 z).mpr hz)
    simp [hb]
end

#print axioms solution
