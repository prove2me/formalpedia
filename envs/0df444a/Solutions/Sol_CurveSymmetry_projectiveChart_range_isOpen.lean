-- Prove2me | solution 1 for CurveSymmetry.projectiveChart_range_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:44.043511+00:00
-- url     : https://prove2.me/submissions/beb7bef7-116e-4742-bbe6-b74bb1f92e37

-- Solution generated from lean/ProjectiveAtlasOpenCover.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_affineLinePoint_range
import Theorems.Thm_CurveSymmetry_reciprocalLinePoint_range
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
noncomputable section
open OnePoint
set_option autoImplicit false
theorem affineLinePoint_injective : Function.Injective affineLinePoint := by
  intro x y h
  change sphereProjectiveEquiv (x : Sphere) = sphereProjectiveEquiv (y : Sphere) at h
  exact OnePoint.coe_injective (sphereProjectiveEquiv.injective h)
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem reciprocalLinePoint_injective : Function.Injective reciprocalLinePoint := by
  intro x y h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h0
  simpa [h0] using h1.symm
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
private lemma pair_chart_range (f g : ℂ → ProjectiveLine)
    (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range (fun w : Fin 2 → ℂ => (f (w 0), g (w 1))) ↔
      p.1 ∈ Set.range f ∧ p.2 ∈ Set.range g := by
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨⟨w 0, rfl⟩, ⟨w 1, rfl⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨![x, y], Prod.ext hx hy⟩
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem affineProjectiveChart_range (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range affineProjectiveChart ↔
      p.1 ≠ sphereProjectiveEquiv (∞ : Sphere) ∧
      p.2 ≠ sphereProjectiveEquiv (∞ : Sphere) := by
  unfold affineProjectiveChart
  rw [pair_chart_range, affineLinePoint_range, affineLinePoint_range]
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem mixedProjectiveChart_range (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range mixedProjectiveChart ↔
      p.1 ≠ affineLinePoint 0 ∧ p.2 ≠ sphereProjectiveEquiv (∞ : Sphere) := by
  unfold mixedProjectiveChart
  rw [pair_chart_range, reciprocalLinePoint_range, affineLinePoint_range]
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem otherMixedProjectiveChart_range (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range otherMixedProjectiveChart ↔
      p.1 ≠ sphereProjectiveEquiv (∞ : Sphere) ∧ p.2 ≠ affineLinePoint 0 := by
  rw [← affineLinePoint_range, ← reciprocalLinePoint_range]
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨⟨w 1, rfl⟩, ⟨w 0, rfl⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨![y, x], Prod.ext hx hy⟩
end
end CurveSymmetry

namespace CurveSymmetry
noncomputable section
open OnePoint
set_option autoImplicit false
theorem reciprocalProjectiveChart_range (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range reciprocalProjectiveChart ↔
      p.1 ≠ affineLinePoint 0 ∧ p.2 ≠ affineLinePoint 0 := by
  unfold reciprocalProjectiveChart
  rw [pair_chart_range,
    reciprocalLinePoint_range, reciprocalLinePoint_range]
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
theorem affineZariski_coordinate_nonzero_open (i : Fin 2) :
    IsOpen {v : Fin 2 → ℂ | v i ≠ 0} := by
  simpa using affineZariski_polynomial_nonzero_open (X i)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasOpenCover
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasOpenCover
theorem projectiveAtlas_isOpen_iff (S : Set (ProjectiveLine × ProjectiveLine)) :
    IsOpen S ↔ ∀ i, IsOpen (projectiveChart i ⁻¹' S) := by
  rw [isOpen_coinduced, isOpen_sigma_iff]
  rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasOpenCover
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasOpenCover
private lemma affine_ne_infinity (z : ℂ) :
    affineLinePoint z ≠ sphereProjectiveEquiv (∞ : Sphere) :=
  (affineLinePoint_range _).mp ⟨z, rfl⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasOpenCover
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasOpenCover
private lemma reciprocal_ne_zero (z : ℂ) :
    reciprocalLinePoint z ≠ affineLinePoint 0 :=
  (reciprocalLinePoint_range _).mp ⟨z, rfl⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasOpenCover
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasOpenCover
private lemma reciprocal_ne_infinity (z : ℂ) :
    reciprocalLinePoint z ≠ sphereProjectiveEquiv (∞ : Sphere) ↔ z ≠ 0 := by
  change reciprocalLinePoint z ≠ reciprocalLinePoint 0 ↔ z ≠ 0
  exact reciprocalLinePoint_injective.ne_iff
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasOpenCover
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasOpenCover
theorem solution (j : Fin 4) : IsOpen (Set.range (projectiveChart j)) := by
  apply (projectiveAtlas_isOpen_iff _).mpr
  intro i
  have h0 := affineZariski_coordinate_nonzero_open 0
  have h1 := affineZariski_coordinate_nonzero_open 1
  have h01 := h0.inter h1
  have h10 := h1.inter h0
  have he (i j : Fin 4) : projectiveChart i ⁻¹' Set.range (projectiveChart j) =
      ![![Set.univ, {v | v 0 ≠ 0}, {v | v 0 ≠ 0}, {v | v 0 ≠ 0 ∧ v 1 ≠ 0}],
        ![{v | v 0 ≠ 0}, Set.univ, {v | v 1 ≠ 0 ∧ v 0 ≠ 0}, {v | v 1 ≠ 0}],
        ![{v | v 1 ≠ 0}, {v | v 0 ≠ 0 ∧ v 1 ≠ 0}, Set.univ, {v | v 0 ≠ 0}],
        ![{v | v 0 ≠ 0 ∧ v 1 ≠ 0}, {v | v 1 ≠ 0}, {v | v 1 ≠ 0}, Set.univ]] j i := by
    ext v
    fin_cases j <;> fin_cases i <;>
      simp only [Set.mem_preimage, projectiveChart, Matrix.cons_val_zero',
        Matrix.cons_val_succ', affineProjectiveChart_range, mixedProjectiveChart_range,
        otherMixedProjectiveChart_range, reciprocalProjectiveChart_range] <;>
      simp [affineProjectiveChart, mixedProjectiveChart, otherMixedProjectiveChart,
        reciprocalProjectiveChart, affine_ne_infinity, reciprocal_ne_zero,
        reciprocal_ne_infinity, affineLinePoint_injective.ne_iff]
  rw [he]
  fin_cases j <;> fin_cases i <;>
    first | exact isOpen_univ | exact h0 | exact h1 | exact h01 | exact h10
end

#print axioms solution
