-- Prove2me | solution 1 for CurveSymmetry.projectiveChart_isOpenEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:22.695097+00:00
-- url     : https://prove2.me/submissions/885eca63-e8a5-49e7-90ae-faaa9fac4d62

-- Solution generated from lean/ProjectiveAtlasEmbeddings.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_affineLinePoint_range
import Theorems.Thm_CurveSymmetry_continuous_invertCoordinate
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
theorem affineProjectiveChart_injective : Function.Injective affineProjectiveChart := by
  intro v w h
  have h0 := affineLinePoint_injective (congrArg Prod.fst h)
  have h1 := affineLinePoint_injective (congrArg Prod.snd h)
  ext i
  fin_cases i <;> assumption
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
theorem affineZariski_coordinate_nonzero_open (i : Fin 2) :
    IsOpen {v : Fin 2 → ℂ | v i ≠ 0} := by
  simpa using affineZariski_polynomial_nonzero_open (X i)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
theorem affineZariski_both_coordinates_nonzero_open :
    IsOpen {v : Fin 2 → ℂ | v 0 ≠ 0 ∧ v 1 ≠ 0} :=
  (affineZariski_coordinate_nonzero_open 0).inter (affineZariski_coordinate_nonzero_open 1)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology
/-- The induced topology has precisely the usual algebraic closure operator:
closure is the common zero set of all polynomials vanishing on the set.
Thus no closure claim is hidden in the choice of topology. -/
theorem affineZariski_closure (S : Set (Fin 2 → ℂ)) :
    closure S = {v | ∀ P ∈ vanishingIdeal ℂ S, eval v P = 0} := by
  rw [affineZariski_embedding.closure_eq_preimage_closure_image,
    ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    spectrum_vanishingIdeal_image]
  rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem polynomialPointMap_eval (F : Fin 2 → BPoly) (v : Fin 2 → ℂ) (P : BPoly) :
    eval (polynomialPointMap F v) P = eval v (eval₂ C F P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simpa only [eval₂_add, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      simp only [map_mul, eval_X, eval₂_mul, eval₂_X, polynomialPointMap]
      rw [hP]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_polynomialZariskiMaps
/-- Polynomial coordinate maps are continuous for the affine Zariski topology.
No Euclidean-continuity theorem or global topology instance is used. -/
theorem polynomialPointMap_continuous (F : Fin 2 → BPoly) :
    Continuous (polynomialPointMap F) := by
  apply continuous_iff_isClosed.mpr
  intro S hS
  have he : S = {v | ∀ P ∈ vanishingIdeal ℂ S, eval v P = 0} :=
    hS.closure_eq.symm.trans (affineZariski_closure S)
  have hpre : polynomialPointMap F ⁻¹' S =
      ⋂ P ∈ vanishingIdeal ℂ S, {v : Fin 2 → ℂ | eval v (eval₂ C F P) = 0} := by
    ext v
    conv_lhs => rw [he]
    simp [polynomialPointMap_eval]
  rw [hpre]
  exact isClosed_biInter (fun P _ => affineZariski_polynomial_zero_closed (eval₂ C F P))
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem exchangeCoordinates_involutive : Function.Involutive exchangeCoordinates := by
  intro v
  ext i
  fin_cases i <;> rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_coordinateExchange
theorem exchangeCoordinates_continuous : Continuous exchangeCoordinates := by
  have he : polynomialPointMap ![X 1, X 0] = exchangeCoordinates := by
    funext v i
    fin_cases i <;> simp [polynomialPointMap, exchangeCoordinates]
  rw [← he]
  exact polynomialPointMap_continuous _
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_coordinateExchange
/-- Coordinate exchange is a homeomorphism for the complex-point Zariski
topology, not just the usual Euclidean topology. -/
def coordinateExchangeHomeomorph : (Fin 2 → ℂ) ≃ₜ (Fin 2 → ℂ) where
  toFun := exchangeCoordinates
  invFun := exchangeCoordinates
  left_inv := exchangeCoordinates_involutive
  right_inv := exchangeCoordinates_involutive
  continuous_toFun := exchangeCoordinates_continuous
  continuous_invFun := exchangeCoordinates_continuous
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_simultaneousInversion
theorem torusInvertCoordinate_continuous (i : Fin 2) : Continuous (torusInvertCoordinate i) := by
  have hn (v : AffineTorus) : v.val i ≠ 0 := by
    fin_cases i
    · exact v.property.1
    · exact v.property.2
  have hc : Continuous (fun v : AffineTorus => (⟨v.val, hn v⟩ : CoordinateNonzero i)) :=
    continuous_subtype_val.subtype_mk _
  exact ((continuous_invertCoordinate i).comp hc).subtype_mk _
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_simultaneousInversion
theorem simultaneousInversion_val (v : AffineTorus) :
    (simultaneousInversion v).val = ![(v.val 0)⁻¹, (v.val 1)⁻¹] := by
  ext i
  fin_cases i <;> simp [simultaneousInversion, torusInvertCoordinate, invertCoordinate]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_simultaneousInversion
theorem simultaneousInversion_involutive : Function.Involutive simultaneousInversion := by
  intro v
  apply Subtype.ext
  rw [simultaneousInversion_val, simultaneousInversion_val]
  ext i
  fin_cases i <;> simp
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_simultaneousInversion
def simultaneousInversionHomeomorph : AffineTorus ≃ₜ AffineTorus where
  toFun := simultaneousInversion
  invFun := simultaneousInversion
  left_inv := simultaneousInversion_involutive
  right_inv := simultaneousInversion_involutive
  continuous_toFun := (torusInvertCoordinate_continuous 1).comp (torusInvertCoordinate_continuous 0)
  continuous_invFun := (torusInvertCoordinate_continuous 1).comp (torusInvertCoordinate_continuous 0)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_simultaneousInversion
/-- The torus homeomorphism is exactly the finite/reciprocal chart transition. -/
theorem simultaneousInversion_chart (v : AffineTorus) :
    reciprocalProjectiveChart v.val = affineProjectiveChart (simultaneousInversion v).val := by
  rw [simultaneousInversion_val]
  exact reciprocalProjectiveChart_overlap v.val v.property.1 v.property.2
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
private lemma reciprocal_ne_infinity (z : ℂ) :
    reciprocalLinePoint z ≠ sphereProjectiveEquiv (∞ : Sphere) ↔ z ≠ 0 := by
  change reciprocalLinePoint z ≠ reciprocalLinePoint 0 ↔ z ≠ 0
  exact reciprocalLinePoint_injective.ne_iff
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasOpenCover
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasOpenCover
/-- Exact affine-chart overlap domains, including the reversed coordinate order
in the second mixed chart. -/
theorem projectiveChart_affine_overlap_domains (i : Fin 4) :
    projectiveChart i ⁻¹' Set.range affineProjectiveChart =
      ![Set.univ, {v | v 0 ≠ 0}, {v | v 0 ≠ 0},
        {v : Fin 2 → ℂ | v 0 ≠ 0 ∧ v 1 ≠ 0}] i := by
  ext v
  fin_cases i <;>
    simp only [Set.mem_preimage, projectiveChart, Matrix.cons_val_zero',
      Matrix.cons_val_succ', affineProjectiveChart_range] <;>
    simp [affineProjectiveChart,
      mixedProjectiveChart, otherMixedProjectiveChart, reciprocalProjectiveChart,
      affine_ne_infinity, reciprocal_ne_infinity]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAffineEmbedding
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAffineEmbedding
private theorem overlap_preimage_open
    (g : (Fin 2 → ℂ) → ProjectiveLine × ProjectiveLine)
    (D : Set (Fin 2 → ℂ)) (hD : IsOpen D)
    (hd : g ⁻¹' Set.range affineProjectiveChart = D)
    (t : D → (Fin 2 → ℂ)) (ht : Continuous t)
    (he : ∀ v : D, g v.val = affineProjectiveChart (t v))
    (U : Set (Fin 2 → ℂ)) (hU : IsOpen U) :
    IsOpen (g ⁻¹' (affineProjectiveChart '' U)) := by
  have hs : g ⁻¹' (affineProjectiveChart '' U) = Subtype.val '' (t ⁻¹' U) := by
    ext v
    constructor
    · rintro ⟨w, hw, hfw⟩
      have hv : v ∈ D := by
        rw [← hd]
        exact ⟨w, hfw⟩
      refine ⟨⟨v, hv⟩, ?_, rfl⟩
      have htval : t ⟨v, hv⟩ = w :=
        affineProjectiveChart_injective ((he ⟨v, hv⟩).symm.trans hfw.symm)
      simpa only [Set.mem_preimage, htval] using hw
    · rintro ⟨v, hv, rfl⟩
      exact ⟨t v, hv, (he v).symm⟩
  rw [hs]
  exact hD.isOpenMap_subtype_val _ (hU.preimage ht)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAffineEmbedding
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAffineEmbedding
/-- The affine chart sends every affine-Zariski open set to an open subset of
the chart-final projective space. The proof checks all other chart preimages
using inversion transitions on their actual nonzero domains. -/
theorem affineProjectiveChart_isOpenMap : IsOpenMap affineProjectiveChart := by
  intro U hU
  apply (projectiveAtlas_isOpen_iff _).mpr
  intro i
  fin_cases i
  · change IsOpen (affineProjectiveChart ⁻¹' (affineProjectiveChart '' U))
    simpa only [Set.preimage_image_eq _ affineProjectiveChart_injective] using hU
  · apply overlap_preimage_open mixedProjectiveChart {v | v 0 ≠ 0}
      (affineZariski_coordinate_nonzero_open 0)
      (projectiveChart_affine_overlap_domains 1)
      (fun v => invertCoordinate 0 v.val) (continuous_invertCoordinate 0) _ U hU
    intro v
    rw [mixedProjectiveChart_overlap v.val v.property]
    congr 1
    ext j
    fin_cases j <;> simp [invertCoordinate]
  · apply overlap_preimage_open otherMixedProjectiveChart {v | v 0 ≠ 0}
      (affineZariski_coordinate_nonzero_open 0)
      (projectiveChart_affine_overlap_domains 2)
      (fun v => exchangeCoordinates (invertCoordinate 0 v.val))
      (exchangeCoordinates_continuous.comp (continuous_invertCoordinate 0)) _ U hU
    intro v
    rw [otherMixedProjectiveChart_overlap v.val v.property]
    congr 1
  · exact overlap_preimage_open reciprocalProjectiveChart
      {v | v 0 ≠ 0 ∧ v 1 ≠ 0} affineZariski_both_coordinates_nonzero_open
      (projectiveChart_affine_overlap_domains 3)
      (fun v => (simultaneousInversion v).val)
      (continuous_subtype_val.comp simultaneousInversionHomeomorph.continuous)
      simultaneousInversion_chart U hU
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAffineEmbedding
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAffineEmbedding
/-- The affine chart has precisely the affine Zariski topology as its subspace
topology, and its image is open. No embedding assumption is used. -/
theorem affineProjectiveChart_isOpenEmbedding :
    Topology.IsOpenEmbedding affineProjectiveChart :=
  .of_continuous_injective_isOpenMap (projectiveChart_continuous 0)
    affineProjectiveChart_injective affineProjectiveChart_isOpenMap
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem projectiveLineFlip_affine (z : ℂ) :
    projectiveLineFlip (affineLinePoint z) = reciprocalLinePoint z := by
  simp only [projectiveLineFlip, affineLinePoint, Projectivization.map_mk]
  rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem projectiveLineFlip_reciprocal (z : ℂ) :
    projectiveLineFlip (reciprocalLinePoint z) = affineLinePoint z := by
  simp only [projectiveLineFlip, reciprocalLinePoint, Projectivization.map_mk]
  rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem projectiveLineFlip_involutive : Function.Involutive projectiveLineFlip := by
  intro p
  rcases projectiveLine_chart_cover p with ⟨z, rfl⟩ | ⟨z, rfl⟩ <;>
    simp only [projectiveLineFlip_affine, projectiveLineFlip_reciprocal]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem projectiveAtlas_continuous_iff (f : (ProjectiveLine × ProjectiveLine) →
    ProjectiveLine × ProjectiveLine) :
    Continuous f ↔ ∀ i, Continuous (f ∘ projectiveChart i) := by
  rw [continuous_coinduced_dom, continuous_sigma_iff]
  rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem projectiveFlipFirst_continuous : Continuous projectiveFlipFirst := by
  apply (projectiveAtlas_continuous_iff _).mpr
  intro i
  fin_cases i
  · exact projectiveChart_continuous 1 |>.congr (fun v => by
      simp [projectiveChart, projectiveFlipFirst,
        affineProjectiveChart, mixedProjectiveChart, projectiveLineFlip_affine])
  · exact projectiveChart_continuous 0 |>.congr (fun v => by
      simp [projectiveChart, projectiveFlipFirst,
        affineProjectiveChart, mixedProjectiveChart, projectiveLineFlip_reciprocal])
  · exact ((projectiveChart_continuous 3).comp exchangeCoordinates_continuous).congr
      (fun v => by simp [projectiveChart, projectiveFlipFirst,
        otherMixedProjectiveChart, reciprocalProjectiveChart, exchangeCoordinates,
        projectiveLineFlip_affine])
  · exact ((projectiveChart_continuous 2).comp exchangeCoordinates_continuous).congr
      (fun v => by simp [projectiveChart, projectiveFlipFirst,
        otherMixedProjectiveChart, reciprocalProjectiveChart, exchangeCoordinates,
        projectiveLineFlip_reciprocal])
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
def projectiveFlipFirstHomeomorph :
    (ProjectiveLine × ProjectiveLine) ≃ₜ (ProjectiveLine × ProjectiveLine) where
  toFun := projectiveFlipFirst
  invFun := projectiveFlipFirst
  left_inv p := Prod.ext (projectiveLineFlip_involutive p.1) rfl
  right_inv p := Prod.ext (projectiveLineFlip_involutive p.1) rfl
  continuous_toFun := projectiveFlipFirst_continuous
  continuous_invFun := projectiveFlipFirst_continuous
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
/-- Factor exchange is continuous for the atlas topology, without assuming
that it is a product topology (which would be wrong for Zariski geometry). -/
theorem projectiveFactorSwap_continuous :
    Continuous (Prod.swap : ProjectiveLine × ProjectiveLine → _) := by
  apply (projectiveAtlas_continuous_iff _).mpr
  intro i
  fin_cases i
  · exact ((projectiveChart_continuous 0).comp exchangeCoordinates_continuous).congr
      (fun _ => rfl)
  · exact (projectiveChart_continuous 2).congr (fun _ => rfl)
  · exact (projectiveChart_continuous 1).congr (fun _ => rfl)
  · exact ((projectiveChart_continuous 3).comp exchangeCoordinates_continuous).congr
      (fun _ => rfl)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
def projectiveFactorSwapHomeomorph :
    (ProjectiveLine × ProjectiveLine) ≃ₜ (ProjectiveLine × ProjectiveLine) where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := projectiveFactorSwap_continuous
  continuous_invFun := projectiveFactorSwap_continuous
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem mixedProjectiveChart_isOpenEmbedding :
    Topology.IsOpenEmbedding mixedProjectiveChart := by
  have h := projectiveFlipFirstHomeomorph.isOpenEmbedding.comp
    affineProjectiveChart_isOpenEmbedding
  have he : projectiveFlipFirstHomeomorph ∘ affineProjectiveChart = mixedProjectiveChart := by
    funext v
    simp [projectiveFlipFirstHomeomorph, projectiveFlipFirst,
      affineProjectiveChart, mixedProjectiveChart, projectiveLineFlip_affine]
  rwa [he] at h
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem otherMixedProjectiveChart_isOpenEmbedding :
    Topology.IsOpenEmbedding otherMixedProjectiveChart :=
  projectiveFactorSwapHomeomorph.isOpenEmbedding.comp mixedProjectiveChart_isOpenEmbedding
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem reciprocalProjectiveChart_isOpenEmbedding :
    Topology.IsOpenEmbedding reciprocalProjectiveChart := by
  have h := projectiveFlipFirstHomeomorph.isOpenEmbedding.comp
    (otherMixedProjectiveChart_isOpenEmbedding.comp coordinateExchangeHomeomorph.isOpenEmbedding)
  have he : projectiveFlipFirstHomeomorph ∘
      (otherMixedProjectiveChart ∘ coordinateExchangeHomeomorph) = reciprocalProjectiveChart := by
    funext v
    have hc : ⇑coordinateExchangeHomeomorph = exchangeCoordinates := rfl
    simp [Function.comp_def, projectiveFlipFirstHomeomorph, projectiveFlipFirst,
      otherMixedProjectiveChart, reciprocalProjectiveChart, hc,
      exchangeCoordinates, projectiveLineFlip_affine]
  rwa [he] at h
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
attribute [local instance] CurveSymmetry.instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings
attribute [local instance] CurveSymmetry.instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings
theorem solution (i : Fin 4) :
    Topology.IsOpenEmbedding (projectiveChart i) := by
  fin_cases i
  · exact affineProjectiveChart_isOpenEmbedding
  · exact mixedProjectiveChart_isOpenEmbedding
  · exact otherMixedProjectiveChart_isOpenEmbedding
  · exact reciprocalProjectiveChart_isOpenEmbedding
end

#print axioms solution
