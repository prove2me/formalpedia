-- Prove2me | solution 1 for CurveSymmetry.projectiveAtlasTopology_characterization
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:55.490738+00:00
-- url     : https://prove2.me/submissions/176ab8f4-0879-49d5-b159-5bb14686d37e

-- Solution generated from lean/ProjectiveAtlasUniqueness.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_projectiveChart_isOpenEmbedding
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
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasTopology
theorem projectiveAtlasMap_surjective : Function.Surjective projectiveAtlasMap := by
  intro p
  rcases projectiveChart_cover p with ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨⟨0, v⟩, hv⟩
  · exact ⟨⟨1, v⟩, hv⟩
  · exact ⟨⟨2, v⟩, hv⟩
  · exact ⟨⟨3, v⟩, hv⟩
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
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasUniqueness
/-- The standard affine Zariski charts determine at most one topology on the
projective product in which they are open embeddings. Together with the
constructed embeddings, this characterizes the topology by its affine atlas,
independently of any curve equation. -/
theorem projectiveAtlasTopology_unique
    (t : TopologicalSpace (ProjectiveLine × ProjectiveLine))
    (h : ∀ i, @Topology.IsOpenEmbedding _ _ affineZariskiTopology t (projectiveChart i)) :
    t = projectiveAtlasTopology := by
  let := t
  apply TopologicalSpace.ext
  funext S
  apply propext
  change IsOpen S ↔ @IsOpen _ projectiveAtlasTopology S
  rw [projectiveAtlas_isOpen_iff]
  constructor
  · intro hs i
    exact hs.preimage (h i).continuous
  · intro hs
    have he : S = ⋃ i, projectiveChart i '' (projectiveChart i ⁻¹' S) := by
      ext p
      constructor
      · intro hp
        obtain ⟨⟨i, v⟩, hv⟩ := projectiveAtlasMap_surjective p
        change projectiveChart i v = p at hv
        exact Set.mem_iUnion.mpr ⟨i, ⟨v, by simpa only [Set.mem_preimage, hv] using hp, hv⟩⟩
      · intro hp
        obtain ⟨i, v, hv, rfl⟩ := Set.mem_iUnion.mp hp
        exact hv
    rw [he]
    exact isOpen_iUnion (fun i => (h i).isOpenMap _ (hs i))
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasUniqueness
theorem solution
    (t : TopologicalSpace (ProjectiveLine × ProjectiveLine)) :
    (∀ i, @Topology.IsOpenEmbedding _ _ affineZariskiTopology t (projectiveChart i)) ↔
      t = projectiveAtlasTopology := by
  constructor
  · exact projectiveAtlasTopology_unique t
  · rintro rfl
    exact projectiveChart_isOpenEmbedding
end

#print axioms solution
