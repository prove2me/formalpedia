-- Prove2me | solution 1 for CurveSymmetry.radial_realLocus_is_circle
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:32.229864+00:00
-- url     : https://prove2.me/submissions/77eadcad-fefe-4748-b2de-e33221595410

-- Solution generated from lean/RealLocus.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma mem_realLocus_radial {a r z : ℂ} (ha : a ≠ 0) :
    z ∈ realLocus (C a * ((X 0 : BPoly) * X 1 - C r)) ↔ z * star z = r := by
  simp [realLocus, ha, sub_eq_zero]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly}
    (hinf : (realLocus P).Infinite)
    (hform : ∃ a r : ℂ, a ≠ 0 ∧ P = C a * ((X 0 : BPoly) * X 1 - C r)) :
    ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere (0 : ℂ) R := by
  obtain ⟨a, r, ha, rfl⟩ := hform
  obtain ⟨z, hz, hzne⟩ := hinf.exists_notMem_finite (Set.finite_singleton (0 : ℂ))
  have hz0 : z ≠ 0 := by simpa using hzne
  have hr : r = (Complex.normSq z : ℂ) := by
    rw [mem_realLocus_radial ha] at hz
    simpa [Complex.mul_conj] using hz.symm
  refine ⟨‖z‖, norm_pos_iff.mpr hz0, ?_⟩
  ext w
  rw [mem_realLocus_radial ha, hr]
  simp only [Metric.mem_sphere, dist_zero_right, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_inj, Complex.normSq_eq_norm_sq]
  exact sq_eq_sq₀ (norm_nonneg w) (norm_nonneg z)
end

#print axioms solution
