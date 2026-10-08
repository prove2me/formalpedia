-- Prove2me | solution 1 for CurveSymmetry.mixed_corner_mem_chart_closure
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:38.83856+00:00
-- url     : https://prove2.me/submissions/dfe2c4df-56cb-4e70-9d30-07c70c03470a

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
/-- In the mixed chart `u=1/X`, the locus with `u ≠ 0` is Zariski dense in
the whole chart curve, including its origin representing `(∞,0)`. -/
theorem mixed_chart_punctured_closure {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    closure (PrimeSpectrum.zeroLocus ({familyMixedPolynomial m a b} : Set BPoly) ∩
      {p : PrimeSpectrum BPoly | (X 0 : BPoly) ∉ p.asIdeal}) =
      PrimeSpectrum.zeroLocus ({familyMixedPolynomial m a b} : Set BPoly) :=
  hypersurface_deleted_axis_closure _ _ coordinate_zero_irreducible (mixed_not_dvd_coordinate hm a b)
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure (PrimeSpectrum.zeroLocus ({familyMixedPolynomial m a b} : Set BPoly) ∩
        {p : PrimeSpectrum BPoly | (X 0 : BPoly) ∉ p.asIdeal}) := by
  rw [mixed_chart_punctured_closure hm]
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  change eval ![0, 0] (familyMixedPolynomial m a b) = 0
  simp [familyMixedPolynomial, hm.ne']
end

#print axioms solution
