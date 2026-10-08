-- Prove2me | solution 1 for CurveSymmetry.mixed_corner_mem_complex_closure
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:39.804989+00:00
-- url     : https://prove2.me/submissions/3c3d1f67-1ec0-4ca9-82de-5373ad8ba627

-- Solution generated from lean/MixedCornerClosure.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Theorems.Thm_CurveSymmetry_hypersurface_deleted_divisor_closure
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_C (x y c : ℂ) : planeEval x y (C c) = c := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_X_zero (x y : ℂ) : planeEval x y (X 0) = x := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma planeEval_X_one (x y : ℂ) : planeEval x y (X 1) = y := by simp [planeEval]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Specialization to one irreducible deleted divisor. -/
theorem hypersurface_deleted_axis_closure (F u : BPoly) (hu : Irreducible u)
    (hnot : ¬ u ∣ F) :
    closure (PrimeSpectrum.zeroLocus ({F} : Set BPoly) ∩
      {p : PrimeSpectrum BPoly | u ∉ p.asIdeal}) =
      PrimeSpectrum.zeroLocus ({F} : Set BPoly) := by
  apply hypersurface_deleted_divisor_closure F u
  · intro h; apply hnot; simp [h]
  · intro q hq hqF hd
    exact hnot ((hq.associated_of_dvd hu hd).symm.dvd.trans hqF)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma coordinate_zero_irreducible : Irreducible (X 0 : BPoly) := by
  have h := (Polynomial.irreducible_X (R := UPoly)).map toNested.symm.toMulEquiv
  have he : toNested.symm Polynomial.X = (X 0 : BPoly) := by
    apply toNested.injective
    rw [AlgEquiv.apply_symm_apply, toNested_X_zero]
  change Irreducible (toNested.symm Polynomial.X) at h
  rwa [he] at h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma mixed_not_dvd_coordinate {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    ¬ (X 0 : BPoly) ∣ familyMixedPolynomial m a b := by
  rintro ⟨Q, he⟩
  have h := congrArg (planeEval 0 1) he
  simp [familyMixedPolynomial, hm.ne'] at h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
private lemma affineSpectrumPoint_asIdeal (v : Fin 2 → ℂ) :
    (affineSpectrumPoint v).asIdeal = vanishingIdeal ℂ {v} := by
  ext P
  rw [mem_vanishingIdeal_singleton_iff]
  rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma closedPoint_iff_affineSpectrumPoint (p : PrimeSpectrum BPoly) :
    p ∈ closedPoints (PrimeSpectrum BPoly) ↔ ∃ v, affineSpectrumPoint v = p := by
  rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ h
    refine ⟨v, PrimeSpectrum.ext ?_⟩
    rw [affineSpectrumPoint_asIdeal, hv]
  · rintro ⟨v, rfl⟩
    rw [affineSpectrumPoint_asIdeal]
    infer_instance
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma punctured_complex_points_image (F u : BPoly) :
    affineSpectrumPoint '' {v : Fin 2 → ℂ | eval v F = 0 ∧ eval v u ≠ 0} =
      (PrimeSpectrum.zeroLocus ({F} : Set BPoly) ∩
        {p : PrimeSpectrum BPoly | u ∉ p.asIdeal}) ∩ closedPoints (PrimeSpectrum BPoly) := by
  ext p
  constructor
  · rintro ⟨v, ⟨hF, hu⟩, rfl⟩
    refine ⟨⟨?_, hu⟩, (closedPoint_iff_affineSpectrumPoint _).mpr ⟨v, rfl⟩⟩
    intro q hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact hF
  · rintro ⟨⟨hF, hu⟩, hc⟩
    obtain ⟨v, rfl⟩ := (closedPoint_iff_affineSpectrumPoint p).mp hc
    exact ⟨v, ⟨hF (Set.mem_singleton F), hu⟩, rfl⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Specialization of complex-point density to one irreducible divisor. -/
theorem punctured_complex_points_closure (F u : BPoly) (hu : Irreducible u)
    (hnot : ¬ u ∣ F) :
    closure (affineSpectrumPoint '' {v : Fin 2 → ℂ | eval v F = 0 ∧ eval v u ≠ 0}) =
      PrimeSpectrum.zeroLocus ({F} : Set BPoly) := by
  rw [punctured_complex_points_image,
    JacobsonSpace.closure_inter_closedPoints_eq_closure,
    hypersurface_deleted_axis_closure F u hu hnot]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isLocallyClosed.inter
    (PrimeSpectrum.basicOpen u).isOpen.isLocallyClosed
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
        eval v (familyMixedPolynomial m a b) = 0 ∧ v 0 ≠ 0}) := by
  have he : {v : Fin 2 → ℂ | eval v (familyMixedPolynomial m a b) = 0 ∧ v 0 ≠ 0} =
      {v : Fin 2 → ℂ | eval v (familyMixedPolynomial m a b) = 0 ∧ eval v (X 0) ≠ 0} := by simp
  rw [he, punctured_complex_points_closure _ _ coordinate_zero_irreducible
    (mixed_not_dvd_coordinate hm a b)]
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  change eval ![0, 0] (familyMixedPolynomial m a b) = 0
  simp [familyMixedPolynomial, hm.ne']
end

#print axioms solution
