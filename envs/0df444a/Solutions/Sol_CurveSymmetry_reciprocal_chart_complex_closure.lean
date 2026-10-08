-- Prove2me | solution 1 for CurveSymmetry.reciprocal_chart_complex_closure
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:52.390983+00:00
-- url     : https://prove2.me/submissions/c7d2767b-6321-421f-95e9-157b005f13bb

-- Solution generated from lean/ReciprocalCornerClosure.lean (curve-symmetry-lean): inlined helpers in
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
/-- The punctured hypersurface is already dense using ordinary complex
evaluation points; generic spectral points are not being substituted for them. -/
theorem complex_points_deleted_divisor_closure (F u : BPoly) (hF0 : F ≠ 0)
    (havoid : ∀ q : BPoly, Irreducible q → q ∣ F → ¬ q ∣ u) :
    closure (affineSpectrumPoint '' {v : Fin 2 → ℂ | eval v F = 0 ∧ eval v u ≠ 0}) =
      PrimeSpectrum.zeroLocus ({F} : Set BPoly) := by
  rw [punctured_complex_points_image,
    JacobsonSpace.closure_inter_closedPoints_eq_closure,
    hypersurface_deleted_divisor_closure F u hF0 havoid]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isLocallyClosed.inter
    (PrimeSpectrum.basicOpen u).isOpen.isLocallyClosed
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma coordinate_one_irreducible : Irreducible (X 1 : BPoly) := by
  have h := coordinate_zero_irreducible.map
    (renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).toMulEquiv
  change Irreducible (rename (Equiv.swap (0 : Fin 2) 1) (X 0 : BPoly)) at h
  simpa using h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma infinity_not_dvd_coordinates {m : ℕ} (hm : 0 < m) (α : ℂ) :
    ¬ (X 0 : BPoly) ∣ familyInfinityPolynomial m α ∧
    ¬ (X 1 : BPoly) ∣ familyInfinityPolynomial m α := by
  constructor
  · rintro ⟨Q, he⟩
    have h := congrArg (planeEval 0 1) he
    simp [familyInfinityPolynomial, fourTermForm, binaryForm, hm.ne'] at h
  · rintro ⟨Q, he⟩
    have h := congrArg (planeEval 1 0) he
    simp [familyInfinityPolynomial, fourTermForm, binaryForm, hm.ne'] at h
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
      eval v (familyInfinityPolynomial m α) = 0 ∧ v 0 ≠ 0 ∧ v 1 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyInfinityPolynomial m α} : Set BPoly) := by
  have hn := infinity_not_dvd_coordinates hm α
  have he : {v : Fin 2 → ℂ |
      eval v (familyInfinityPolynomial m α) = 0 ∧ v 0 ≠ 0 ∧ v 1 ≠ 0} =
      {v : Fin 2 → ℂ | eval v (familyInfinityPolynomial m α) = 0 ∧
        eval v (X 0 * X 1) ≠ 0} := by simp
  rw [he]
  apply complex_points_deleted_divisor_closure
  · intro h; exact hn.1 (h ▸ dvd_zero _)
  · intro q hq hqF hd
    rcases hq.prime.dvd_mul.mp hd with h0 | h1
    · exact hn.1 ((hq.associated_of_dvd coordinate_zero_irreducible h0).symm.dvd.trans hqF)
    · exact hn.2 ((hq.associated_of_dvd coordinate_one_irreducible h1).symm.dvd.trans hqF)
end

#print axioms solution
