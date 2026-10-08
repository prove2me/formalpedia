-- Prove2me | solution 1 for CurveSymmetry.mixed_affine_points_closure
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:38.086212+00:00
-- url     : https://prove2.me/submissions/2ad54e43-b3f0-4244-b712-68e1ae3e76f6

-- Solution generated from lean/AffineChartImages.lean (curve-symmetry-lean): inlined helpers in
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
lemma fourTermForm_eval (m : ℕ) (a b c d x y : ℂ) :
    planeEval x y (fourTermForm m a b c d) =
      a * x ^ m + b * y ^ m + x * y * (c * x ^ m + d * y ^ m) := by
  simp [fourTermForm, binaryForm]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma family_fourTerm (m : ℕ) (α : ℂ) :
    familyPolynomial m α = fourTermForm m α (star α) 1 1 := by
  simp only [familyPolynomial, fourTermForm, binaryForm, map_one, one_mul]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- The chart with `u=1/X` and `Y` unchanged. -/
lemma family_mixed_chart (m : ℕ) (α : ℂ) {u y : ℂ} (hu : u ≠ 0) :
    u ^ (m + 1) * planeEval u⁻¹ y (familyPolynomial m α) =
      planeEval u y (familyMixedPolynomial m α (star α)) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyMixedPolynomial, map_add, map_mul, map_pow, planeEval_C,
    planeEval_X_zero, planeEval_X_one, pow_succ, inv_pow, one_mul]
  field_simp
  ring
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

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
private lemma vector_eta (z : Fin 2 → ℂ) : ![z 0, z 1] = z := by
  ext i
  fin_cases i <;> rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
private lemma planeEval_vector (x y : ℂ) : planeEval x y = eval ![x, y] := by
  unfold planeEval
  congr 1
  funext i
  fin_cases i <;> rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma mixed_vector_zero_iff (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) (hw : w 0 ≠ 0) :
    eval w (familyMixedPolynomial m α (star α)) = 0 ↔
      eval ![(w 0)⁻¹, w 1] (familyPolynomial m α) = 0 := by
  have h := family_mixed_chart m α (y := w 1) hw
  rw [planeEval_vector, planeEval_vector, vector_eta] at h
  rw [← h, mul_eq_zero]
  simp [pow_ne_zero _ hw]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
/-- Inverting the first coordinate identifies original affine points with
`X ≠ 0` and the punctured first mixed chart, in both directions. -/
theorem mixed_affine_points_image (m : ℕ) (α : ℂ) :
    (fun z : Fin 2 → ℂ => ![(z 0)⁻¹, z 1]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0} =
      {w : Fin 2 → ℂ | eval w (familyMixedPolynomial m α (star α)) = 0 ∧
        w 0 ≠ 0} := by
  apply Set.Subset.antisymm
  · rintro w ⟨z, ⟨hz, h0⟩, rfl⟩
    refine ⟨(mixed_vector_zero_iff m α _ (inv_ne_zero h0)).mpr ?_, inv_ne_zero h0⟩
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      inv_inv, vector_eta] using hz
  · rintro w ⟨hw, h0⟩
    refine ⟨![(w 0)⁻¹, w 1],
      ⟨(mixed_vector_zero_iff m α w h0).mp hw, inv_ne_zero h0⟩, ?_⟩
    simpa using vector_eta w
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure ((fun z : Fin 2 → ℂ => affineSpectrumPoint ![(z 0)⁻¹, z 1]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyMixedPolynomial m α (star α)} : Set BPoly) := by
  have he := congrArg (Set.image affineSpectrumPoint) (mixed_affine_points_image m α)
  rw [Set.image_image] at he
  rw [he]
  simpa using punctured_complex_points_closure _ _ coordinate_zero_irreducible
    (mixed_not_dvd_coordinate hm α (star α))
end

#print axioms solution
