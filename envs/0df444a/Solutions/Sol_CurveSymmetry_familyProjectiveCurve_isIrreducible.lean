-- Prove2me | solution 1 for CurveSymmetry.familyProjectiveCurve_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:42.98598+00:00
-- url     : https://prove2.me/submissions/21a1e3ae-e520-4750-b1f9-68bc6c5479fd

-- Solution generated from lean/ProjectiveCurveIrreducibility.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_family_point_of_norm
import Theorems.Thm_CurveSymmetry_family_projective_chart_gluing
import Theorems.Thm_CurveSymmetry_real_diagonal_vanishingIdeal
import Theorems.Thm_CurveSymmetry_spectrum_vanishingIdeal_image
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
import Mathlib.Topology.Constructions

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem family_realLocus_infinite {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    (realLocus (familyPolynomial m α)).Infinite := by
  have hex : ∀ n : ℕ, ∃ z ∈ realLocus (familyPolynomial m α), ‖z‖ = (n : ℝ) + 1 := by
    intro n
    exact family_point_of_norm hm ha (by positivity)
  choose f hf hnorm using hex
  have hinj : Function.Injective f := by
    intro n k h
    have he := congrArg norm h
    rw [hnorm, hnorm] at he
    exact_mod_cast (add_right_cancel he)
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨n, rfl⟩; exact hf n)
end CurveSymmetry

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
/-- Genuine Zariski closure in Mathlib's affine prime spectrum. This is the
affine closure statement; projective boundary closure remains separate. -/
theorem real_diagonal_spectrum_closure {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) :
    closure (affineSpectrumPoint '' affineRealDiagonal P) =
      PrimeSpectrum.zeroLocus ({P} : Set BPoly) := by
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    spectrum_vanishingIdeal_image, real_diagonal_vanishingIdeal hP hinf,
    PrimeSpectrum.zeroLocus_span]
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
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
theorem affineZariski_polynomial_nonzero_open (P : BPoly) :
    IsOpen {v : Fin 2 → ℂ | eval v P ≠ 0} := by
  exact (PrimeSpectrum.basicOpen P).isOpen.preimage affineZariski_embedding.continuous
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
theorem affineZariski_polynomial_zero_closed (P : BPoly) :
    IsClosed {v : Fin 2 → ℂ | eval v P = 0} := by
  simpa only [Set.compl_ofPred, not_not] using
    (affineZariski_polynomial_nonzero_open P).isClosed_compl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
/-- The previous spectral closure theorem now gives an actual closure theorem
on complex coordinate points with their Zariski topology. -/
theorem affineZariski_real_diagonal_closure {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) :
    closure (affineRealDiagonal P) = {v : Fin 2 → ℂ | eval v P = 0} := by
  rw [affineZariski_embedding.closure_eq_preimage_closure_image,
    real_diagonal_spectrum_closure hP hinf]
  ext v
  change (∀ f ∈ ({P} : Set BPoly), eval v f = 0) ↔ eval v P = 0
  simp
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
/-- The family itself satisfies the same chartwise closedness condition. -/
theorem family_closed_in_projective_charts (m : ℕ) (α : ℂ) :
    ClosedInProjectiveCharts (familyProjectiveCurve m α) := by
  have hA : affineProjectiveChart ⁻¹' familyProjectiveCurve m α =
      {v | eval v (familyPolynomial m α) = 0} := by
    ext v; exact (affineProjectiveChart_mem m α v).trans (by simp only [Set.mem_ofPred_eq, eval_plane])
  have hM : mixedProjectiveChart ⁻¹' familyProjectiveCurve m α =
      {v | eval v (familyMixedPolynomial m α (star α)) = 0} := by
    ext v; exact (mixedProjectiveChart_mem m α v).trans (by simp only [Set.mem_ofPred_eq, eval_plane])
  have hO : otherMixedProjectiveChart ⁻¹' familyProjectiveCurve m α =
      {v | eval v (familyMixedPolynomial m (star α) α) = 0} := by
    ext v; exact (otherMixedProjectiveChart_mem m α v).trans (by simp only [Set.mem_ofPred_eq, eval_plane])
  have hR : reciprocalProjectiveChart ⁻¹' familyProjectiveCurve m α =
      {v | eval v (familyInfinityPolynomial m α) = 0} := by
    ext v; exact (reciprocalProjectiveChart_mem m α v).trans (by simp only [Set.mem_ofPred_eq, eval_plane])
  unfold ClosedInProjectiveCharts
  rw [hA, hM, hO, hR]
  exact ⟨affineZariski_polynomial_zero_closed _, affineZariski_polynomial_zero_closed _,
    affineZariski_polynomial_zero_closed _, affineZariski_polynomial_zero_closed _⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveClosureGluing
section AmbientTopology
variable [TopologicalSpace (ProjectiveLine × ProjectiveLine)]
/-- Conditional ambient closure theorem. Its hypotheses expose the remaining
topology interface: four continuous charts and closedness of the projective
equation. No particular projective topology is silently supplied. -/
theorem family_projective_closure_of_chart_continuity {m : ℕ} (hm : 0 < m) (α : ℂ)
    (hA : Continuous affineProjectiveChart) (hM : Continuous mixedProjectiveChart)
    (hO : Continuous otherMixedProjectiveChart) (hR : Continuous reciprocalProjectiveChart)
    (hV : IsClosed (familyProjectiveCurve m α)) :
    closure (affineProjectiveChart '' {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0}) =
      familyProjectiveCurve m α := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ hV
    rintro _ ⟨v, hv, rfl⟩
    exact (affineProjectiveChart_mem m α v).mpr ((eval_plane v _).symm.trans hv)
  · apply family_projective_chart_gluing hm α
    · exact ⟨isClosed_closure.preimage hA, isClosed_closure.preimage hM,
        isClosed_closure.preimage hO, isClosed_closure.preimage hR⟩
    · exact subset_closure
end AmbientTopology
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasTopology
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasTopology
theorem projectiveAtlasMap_continuous : Continuous projectiveAtlasMap :=
  continuous_coinduced_rng
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasTopology
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasTopology
theorem projectiveChart_continuous (i : Fin 4) : Continuous (projectiveChart i) :=
  projectiveAtlasMap_continuous.comp continuous_sigmaMk
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasTopology
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasTopology
/-- Closedness in this family-independent final topology is exactly the
previously defined chartwise closedness predicate. -/
theorem projectiveAtlas_isClosed_iff (S : Set (ProjectiveLine × ProjectiveLine)) :
    IsClosed S ↔ ClosedInProjectiveCharts S := by
  rw [isClosed_coinduced, isClosed_sigma_iff]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> assumption
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasClosure
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasClosure
theorem family_projectiveAtlas_isClosed (m : ℕ) (α : ℂ) :
    IsClosed (familyProjectiveCurve m α) :=
  (projectiveAtlas_isClosed_iff _).mpr (family_closed_in_projective_charts m α)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasClosure
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasClosure
/-- Closure in the family-independent chart-final topology. Identification of
that topology with standard projective Zariski geometry is a separate task. -/
theorem family_projectiveAtlas_affine_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure (affineProjectiveChart '' {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0}) =
      familyProjectiveCurve m α :=
  family_projective_closure_of_chart_continuity hm α
    (projectiveChart_continuous 0) (projectiveChart_continuous 1)
    (projectiveChart_continuous 2) (projectiveChart_continuous 3)
    (family_projectiveAtlas_isClosed m α)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasClosure
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasClosure
/-- The real diagonal already has the entire complex curve as its closure in
the chart-final topology, including the three boundary points. -/
theorem family_projectiveAtlas_real_closure {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) :
    closure (affineProjectiveChart '' affineRealDiagonal (familyPolynomial m α)) =
      familyProjectiveCurve m α := by
  have hc := affineZariski_real_diagonal_closure
    (familyPolynomial_irreducible hm ha) (family_realLocus_infinite hm ha)
  apply Set.Subset.antisymm
  · calc
      closure (affineProjectiveChart '' affineRealDiagonal (familyPolynomial m α)) ⊆
          closure (affineProjectiveChart ''
            {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0}) := by
        apply closure_mono (Set.image_mono _)
        rw [← hc]
        exact subset_closure
      _ = familyProjectiveCurve m α := family_projectiveAtlas_affine_closure hm α
  · apply family_projective_chart_gluing hm α
    · exact (projectiveAtlas_isClosed_iff _).mp isClosed_closure
    · have hd : affineRealDiagonal (familyPolynomial m α) ⊆
          affineProjectiveChart ⁻¹'
            closure (affineProjectiveChart '' affineRealDiagonal (familyPolynomial m α)) := by
        intro v hv
        exact subset_closure ⟨v, hv, rfl⟩
      have he := closure_minimal hd
        (isClosed_closure.preimage (projectiveChart_continuous 0))
      rw [hc] at he
      rintro _ ⟨v, hv, rfl⟩
      exact he hv
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveCurveIrreducibility
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveCurveIrreducibility
private theorem affine_irreducible_of_spectrum_image (S : Set (Fin 2 → ℂ))
    (h : IsIrreducible (affineSpectrumPoint '' S)) : IsIrreducible S := by
  refine ⟨?_, ?_⟩
  · obtain ⟨_, v, hv, rfl⟩ := h.nonempty
    exact ⟨v, hv⟩
  · intro U V hU hV hSU hSV
    obtain ⟨A, hA, rfl⟩ := affineZariski_embedding.isInducing.isOpen_iff.mp hU
    obtain ⟨B, hB, rfl⟩ := affineZariski_embedding.isInducing.isOpen_iff.mp hV
    obtain ⟨u, hu, hAu⟩ := hSU
    obtain ⟨v, hv, hBv⟩ := hSV
    obtain ⟨_, ⟨w, hw, rfl⟩, hAw, hBw⟩ := h.2 A B hA hB
      ⟨affineSpectrumPoint u, ⟨u, hu, rfl⟩, hAu⟩
      ⟨affineSpectrumPoint v, ⟨v, hv, rfl⟩, hBv⟩
    exact ⟨w, hw, hAw, hBw⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveCurveIrreducibility
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveCurveIrreducibility
/-- The actual real diagonal is irreducible in the complex affine Zariski
topology, not in its Euclidean topology. -/
theorem affineRealDiagonal_isIrreducible {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) : IsIrreducible (affineRealDiagonal P) := by
  apply affine_irreducible_of_spectrum_image
  apply PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mpr
  rw [spectrum_vanishingIdeal_image, real_diagonal_vanishingIdeal hP hinf]
  exact Ideal.isPrime_span_singleton_of_prime hP.prime
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveCurveIrreducibility
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveCurveIrreducibility
theorem solution {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) : IsIrreducible (familyProjectiveCurve m α) := by
  rw [← family_projectiveAtlas_real_closure hm ha]
  exact ((affineRealDiagonal_isIrreducible (familyPolynomial_irreducible hm ha)
    (family_realLocus_infinite hm ha)).image affineProjectiveChart
      (projectiveChart_continuous 0).continuousOn).closure
end

#print axioms solution
