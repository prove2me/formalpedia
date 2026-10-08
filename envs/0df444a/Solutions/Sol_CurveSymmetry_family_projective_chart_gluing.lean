-- Prove2me | solution 1 for CurveSymmetry.family_projective_chart_gluing
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:16.939984+00:00
-- url     : https://prove2.me/submissions/b53cf8fe-dcce-418e-bafd-d6e5eb8462c6

-- Solution generated from lean/ProjectiveClosureGluing.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_hypersurface_deleted_divisor_closure
import Theorems.Thm_CurveSymmetry_other_mixed_affine_points_image
import Theorems.Thm_CurveSymmetry_reciprocal_chart_complex_closure
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

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
/-- Clearing the two inversion denominators gives the reciprocal chart equation. -/
lemma family_reciprocal_chart (m : ℕ) (α : ℂ) {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (u * v) ^ (m + 1) * planeEval u⁻¹ v⁻¹ (familyPolynomial m α) =
      planeEval u v (familyInfinityPolynomial m α) := by
  rw [family_fourTerm, fourTermForm_eval, familyInfinityPolynomial, fourTermForm_eval]
  simp only [mul_pow, pow_succ, inv_pow, one_mul]
  field_simp
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
open OnePoint
lemma familyBihomogeneous_smul_left (m : ℕ) (α a : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α (a • x) y = a ^ (m + 1) * familyBihomogeneous m α x y := by
  simp only [familyBihomogeneous, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_smul_right (m : ℕ) (α a : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α x (a • y) = a ^ (m + 1) * familyBihomogeneous m α x y := by
  simp only [familyBihomogeneous, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem familyProjective_mk_iff (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ familyProjectiveCurve m α ↔
      familyBihomogeneous m α x y = 0 := by
  change familyBihomogeneous m α (Projectivization.mk ℂ x hx).rep
    (Projectivization.mk ℂ y hy).rep = 0 ↔ _
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y hy
  rw [← ha, ← hb]
  simp [Units.smul_def, familyBihomogeneous_smul_left, familyBihomogeneous_smul_right]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_affine (m : ℕ) (α x y : ℂ) :
    familyBihomogeneous m α ![x, 1] ![y, 1] = planeEval x y (familyPolynomial m α) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_reciprocal (m : ℕ) (α u v : ℂ) :
    familyBihomogeneous m α ![1, u] ![1, v] =
      planeEval u v (familyInfinityPolynomial m α) := by
  rw [familyInfinityPolynomial, fourTermForm_eval]
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, one_mul]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_mixed (m : ℕ) (α u y : ℂ) :
    familyBihomogeneous m α ![1, u] ![y, 1] =
      planeEval u y (familyMixedPolynomial m α (star α)) := by
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, one_mul, familyMixedPolynomial,
    map_add, map_mul, map_pow, planeEval_C, planeEval_X_zero, planeEval_X_one]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma familyBihomogeneous_other_mixed (m : ℕ) (α x v : ℂ) :
    familyBihomogeneous m α ![x, 1] ![1, v] =
      planeEval v x (familyMixedPolynomial m (star α) α) := by
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, familyMixedPolynomial,
    map_add, map_mul, map_pow, planeEval_C, planeEval_X_zero, planeEval_X_one]
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
lemma reciprocal_vector_zero_iff (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ)
    (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) :
    eval w (familyInfinityPolynomial m α) = 0 ↔
      eval ![(w 0)⁻¹, (w 1)⁻¹] (familyPolynomial m α) = 0 := by
  have h := family_reciprocal_chart m α h0 h1
  rw [planeEval_vector, planeEval_vector, vector_eta] at h
  rw [← h, mul_eq_zero]
  simp [pow_ne_zero _ (mul_ne_zero h0 h1)]
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem reciprocalLinePoint_overlap {z : ℂ} (hz : z ≠ 0) :
    reciprocalLinePoint z = affineLinePoint z⁻¹ := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨z, ?_⟩
  ext i
  fin_cases i <;> simp [hz]
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem mixedProjectiveChart_overlap (w : Fin 2 → ℂ) (h0 : w 0 ≠ 0) :
    mixedProjectiveChart w = affineProjectiveChart ![(w 0)⁻¹, w 1] := by
  simp [mixedProjectiveChart, affineProjectiveChart, reciprocalLinePoint_overlap h0]
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem otherMixedProjectiveChart_overlap (w : Fin 2 → ℂ) (h0 : w 0 ≠ 0) :
    otherMixedProjectiveChart w = affineProjectiveChart ![w 1, (w 0)⁻¹] := by
  simp [otherMixedProjectiveChart, affineProjectiveChart, reciprocalLinePoint_overlap h0]
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem reciprocalProjectiveChart_overlap (w : Fin 2 → ℂ)
    (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) :
    reciprocalProjectiveChart w = affineProjectiveChart ![(w 0)⁻¹, (w 1)⁻¹] := by
  simp [reciprocalProjectiveChart, affineProjectiveChart,
    reciprocalLinePoint_overlap h0, reciprocalLinePoint_overlap h1]
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem affineProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    affineProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyPolynomial m α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_affine])
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem mixedProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    mixedProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyMixedPolynomial m α (star α)) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_mixed])
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem otherMixedProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    otherMixedProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyMixedPolynomial m (star α) α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_other_mixed])
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem reciprocalProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    reciprocalProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyInfinityPolynomial m α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_reciprocal])
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem projectiveLine_chart_cover (p : ProjectiveLine) :
    (∃ z, affineLinePoint z = p) ∨ (∃ z, reciprocalLinePoint z = p) := by
  obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
  cases u using OnePoint.rec with
  | infty => exact Or.inr ⟨0, rfl⟩
  | coe z => exact Or.inl ⟨z, rfl⟩
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
/-- Every projective pair has coordinates in one of these four injective
charts. This set-theoretic cover does not assert open embeddings. -/
theorem projectiveChart_cover (p : ProjectiveLine × ProjectiveLine) :
    (∃ w, affineProjectiveChart w = p) ∨
    (∃ w, mixedProjectiveChart w = p) ∨
    (∃ w, otherMixedProjectiveChart w = p) ∨
    (∃ w, reciprocalProjectiveChart w = p) := by
  rcases p with ⟨p, q⟩
  rcases projectiveLine_chart_cover p with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases projectiveLine_chart_cover q with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact Or.inl ⟨![x, y], rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨![y, x], rfl⟩))
  · exact Or.inr (Or.inl ⟨![x, y], rfl⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨![x, y], rfl⟩))
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem affineSpectrumPoint_injective : Function.Injective affineSpectrumPoint := by
  intro v w h
  ext i
  have hp : X i - C (v i) ∈ (affineSpectrumPoint v).asIdeal := by
    change eval v (X i - C (v i)) = 0
    simp
  rw [h] at hp
  change eval w (X i - C (v i)) = 0 at hp
  have he : w i - v i = 0 := by simpa using hp
  exact (sub_eq_zero.mp he).symm
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
/-- Evaluation identifies complex points with a topological subspace of the
prime spectrum for the explicitly induced Zariski topology. -/
theorem affineZariski_embedding : Topology.IsEmbedding affineSpectrumPoint :=
  ⟨⟨rfl⟩, affineSpectrumPoint_injective⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveClosureGluing
private lemma eval_plane (v : Fin 2 → ℂ) (P : BPoly) :
    eval v P = planeEval (v 0) (v 1) P := by
  unfold planeEval
  have he : (fun i : Fin 2 => if i = 0 then v 0 else v 1) = v := by
    ext i
    fin_cases i <;> rfl
  rw [he]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveClosureGluing
private theorem chart_closed_extension
    (φ : (Fin 2 → ℂ) → ProjectiveLine × ProjectiveLine)
    (S : Set (ProjectiveLine × ProjectiveLine)) (D : Set (Fin 2 → ℂ)) (Q : BPoly)
    (hs : IsClosed (φ ⁻¹' S)) (hd : φ '' D ⊆ S)
    (hc : closure (affineSpectrumPoint '' D) = PrimeSpectrum.zeroLocus ({Q} : Set BPoly))
    {v : Fin 2 → ℂ} (hv : eval v Q = 0) : φ v ∈ S := by
  have hD : D ⊆ φ ⁻¹' S := by intro w hw; exact hd ⟨w, hw, rfl⟩
  apply closure_minimal hD hs
  rw [affineZariski_embedding.closure_eq_preimage_closure_image, hc]
  change (∀ P ∈ ({Q} : Set BPoly), eval v P = 0)
  simpa using hv
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveClosureGluing
theorem solution {m : ℕ} (hm : 0 < m) (α : ℂ)
    (S : Set (ProjectiveLine × ProjectiveLine)) (hs : ClosedInProjectiveCharts S)
    (hA : affineProjectiveChart '' {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0} ⊆ S) :
    familyProjectiveCurve m α ⊆ S := by
  intro p hp
  rcases projectiveChart_cover p with ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact hA ⟨v, (eval_plane v _).trans ((affineProjectiveChart_mem m α v).mp hp), rfl⟩
  · apply chart_closed_extension mixedProjectiveChart S
      {w | eval w (familyMixedPolynomial m α (star α)) = 0 ∧ w 0 ≠ 0}
      (familyMixedPolynomial m α (star α)) hs.2.1
    · rintro _ ⟨w, ⟨hw, h0⟩, rfl⟩
      exact hA ⟨![(w 0)⁻¹, w 1], (mixed_vector_zero_iff m α w h0).mp hw,
        (mixedProjectiveChart_overlap w h0).symm⟩
    · simpa using punctured_complex_points_closure _ _ coordinate_zero_irreducible
        (mixed_not_dvd_coordinate hm α (star α))
    · exact (eval_plane v _).trans ((mixedProjectiveChart_mem m α v).mp hp)
  · apply chart_closed_extension otherMixedProjectiveChart S
      {w | eval w (familyMixedPolynomial m (star α) α) = 0 ∧ w 0 ≠ 0}
      (familyMixedPolynomial m (star α) α) hs.2.2.1
    · rintro _ ⟨w, hw, rfl⟩
      have hi := (Set.ext_iff.mp (other_mixed_affine_points_image m α) w).mpr hw
      obtain ⟨z, ⟨hz, h1⟩, hzw⟩ := hi
      subst w
      apply hA
      refine ⟨z, hz, ?_⟩
      rw [otherMixedProjectiveChart_overlap _ (inv_ne_zero h1)]
      congr 1
      ext i
      fin_cases i <;> simp
    · simpa using punctured_complex_points_closure _ _ coordinate_zero_irreducible
        (mixed_not_dvd_coordinate hm (star α) α)
    · exact (eval_plane v _).trans ((otherMixedProjectiveChart_mem m α v).mp hp)
  · apply chart_closed_extension reciprocalProjectiveChart S
      {w | eval w (familyInfinityPolynomial m α) = 0 ∧ w 0 ≠ 0 ∧ w 1 ≠ 0}
      (familyInfinityPolynomial m α) hs.2.2.2
    · rintro _ ⟨w, ⟨hw, h0, h1⟩, rfl⟩
      exact hA ⟨![(w 0)⁻¹, (w 1)⁻¹], (reciprocal_vector_zero_iff m α w h0 h1).mp hw,
        (reciprocalProjectiveChart_overlap w h0 h1).symm⟩
    · exact reciprocal_chart_complex_closure hm α
    · exact (eval_plane v _).trans ((reciprocalProjectiveChart_mem m α v).mp hp)
end

#print axioms solution
