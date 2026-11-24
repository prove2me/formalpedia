-- Prove2me | solution 1 for GaussianPerimeter.facet_lintegral_sum_le_gaussianPerimeter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T12:29:34.025371+00:00
-- url     : https://prove2.me/submissions/a3e0f3cf-1a97-499e-9fa2-2b1dcf7f5ca1

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Definitions.Def_GaussianPerimeter_Geometry
public import Theorems.Thm_GaussianPerimeter_inner_facetEmbedding
public import Theorems.Thm_GaussianPerimeter_isometry_facetEmbedding
public import Theorems.Thm_GaussianPerimeter_norm_sq_facetEmbedding
public import Theorems.Thm_GaussianPerimeter_mem_strictFacet
public import Theorems.Thm_GaussianPerimeter_measurableSet_strictFacet
public import Theorems.Thm_GaussianPerimeter_gaussianPerimeter_succ

section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
namespace GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
variable {k : ℕ} {ι : Type*}
private theorem isClosed_halfspaceIntersection (u : ι → Euc (k + 1)) (ρ : ℝ) :
    IsClosed (halfspaceIntersection u ρ) :=
  isClosed_iInter fun i => isClosed_le (innerSL ℝ (u i)).continuous continuous_const
private theorem pairwiseDisjoint_strictFacet (u : ι → Euc (k + 1)) (ρ : ℝ) :
    Pairwise (Disjoint on strictFacet u ρ) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hx hy
  have hx := ((mem_strictFacet u ρ i x).mp hx).2 j hij.symm
  have hy := ((mem_strictFacet u ρ j x).mp hy).1
  exact hx.ne hy
private theorem strictFacet_subset_frontier (u : ι → Euc (k + 1))
    (hu : ∀ i, ‖u i‖ = 1) (ρ : ℝ) (i : ι) :
    strictFacet u ρ i ⊆ frontier (halfspaceIntersection u ρ) := by
  intro x hx
  rw [mem_strictFacet] at hx
  rw [(isClosed_halfspaceIntersection u ρ).frontier_eq]
  refine ⟨mem_iInter.mpr fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst j; exact hx.1.le
    · exact (hx.2 j h).le
  intro hinterior
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hinterior)
  have hclose : x + (ε / 2) • u i ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hconstraint := mem_iInter.mp (hball hclose) i
  change ⟪u i, x + (ε / 2) • u i⟫_ℝ ≤ ρ at hconstraint
  rw [inner_add_right, hx.1, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hu, one_pow, mul_one] at hconstraint
  exact (lt_add_of_pos_right ρ (half_pos hε)).not_ge hconstraint
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
variable {k : ℕ} {ι : Type*}
namespace GaussianPerimeter
theorem _root_.solution [Fintype ι] (u : ι → Euc (k + 1))
    (hu : ∀ i, ‖u i‖ = 1) (ρ : ℝ)
    (hvolume : (volume : Measure (Euc k)) ≤
      (volume (Metric.ball (0 : Euc k) 1) / (2 : ℝ≥0∞) ^ k) • μH[(k : ℝ)]) :
    (∑ i, ∫⁻ y in {y | ∀ j ≠ i, ⟪u j, facetEmbedding (u i) (hu i) ρ y⟫_ℝ < ρ},
      ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
        Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))) ≤
      gaussianPerimeter (halfspaceIntersection u ρ) := by
  classical
  let c := volume (Metric.ball (0 : Euc k) 1) / (2 : ℝ≥0∞) ^ k
  let f (x : Euc (k + 1)) :=
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
  let s i := strictFacet u ρ i
  let μ : Measure (Euc (k + 1)) := c • μH[(k : ℝ)]
  have hsum : (∑ i, ∫⁻ x in s i, f x ∂μ) ≤ gaussianPerimeter (halfspaceIntersection u ρ) := by
    have huEq :
        (∫⁻ x in ⋃ i, s i, f x ∂μ) = ∑ i, ∫⁻ x in s i, f x ∂μ :=
      (lintegral_iUnion (μ := μ) (measurableSet_strictFacet u ρ)
        (pairwiseDisjoint_strictFacet u ρ) f).trans (tsum_fintype _)
    rw [← huEq, gaussianPerimeter_succ]
    change _ ≤ c • ∫⁻ x in frontier (halfspaceIntersection u ρ), f x ∂μH[(k : ℝ)]
    rw [← setLIntegral_smul_measure]
    exact lintegral_mono_set (iUnion_subset (strictFacet_subset_frontier u hu ρ))

  refine (Finset.sum_le_sum fun i _ => ?_).trans hsum
  let e := facetEmbedding (u i) (hu i) ρ
  have he : Isometry e := isometry_facetEmbedding _ _ _
  have hemb : MeasurableEmbedding e := he.isClosedEmbedding.measurableEmbedding
  have hpre :
      e ⁻¹' s i = {y | ∀ j ≠ i, ⟪u j, e y⟫_ℝ < ρ} := by
    ext y
    change (e y ∈ strictFacet u ρ i) ↔ _
    rw [mem_strictFacet]
    simp [e, inner_facetEmbedding]
  have hcomp (y : Euc k) :
      f (e y) = ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
        Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2)) := by
    simp [f, e, norm_sq_facetEmbedding]
  have hmap : Measure.map e (c • μH[(k : ℝ)]) = μ.restrict (range e) := by
    rw [Measure.map_smul,
      he.map_hausdorffMeasure (Or.inl (Nat.cast_nonneg _)), Measure.restrict_smul]
  have hp : MeasurePreserving e (c • μH[(k : ℝ)]) (μ.restrict (range e)) :=
    ⟨hemb.measurable, hmap⟩
  simp_rw [← hcomp]
  rw [← hpre]
  calc
    ∫⁻ y in e ⁻¹' s i, f (e y) ≤
        ∫⁻ y in e ⁻¹' s i, f (e y) ∂(c • μH[(k : ℝ)]) :=
      lintegral_mono' (Measure.restrict_mono Subset.rfl hvolume) (le_refl _)
    _ = ∫⁻ x in s i, f x ∂(μ.restrict (range e)) :=
      hp.setLIntegral_comp_preimage_emb hemb f _
    _ ≤ ∫⁻ x in s i, f x ∂μ :=
      lintegral_mono' (Measure.restrict_mono Subset.rfl Measure.restrict_le_self) (le_refl _)
end GaussianPerimeter
