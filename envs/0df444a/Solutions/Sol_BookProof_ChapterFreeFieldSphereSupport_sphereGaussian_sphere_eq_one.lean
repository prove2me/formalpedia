-- Prove2me | solution 1 for BookProof.ChapterFreeFieldSphereSupport.sphereGaussian_sphere_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:26:19.712451+00:00
-- url     : https://prove2.me/submissions/6b34f243-f30a-4288-a6c5-dac837c69c74

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere in
theorem p8ad8d14e_stdGaussian_zero {n : ℕ} (hn : 0 < n) :
    BookProof.ChapterFreeFieldGaussian.stdGaussian n {(0 : EuclideanSpace ℝ (Fin n))} = 0 := by
  unfold BookProof.ChapterFreeFieldGaussian.stdGaussian
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hpre : (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹'
      {(0 : EuclideanSpace ℝ (Fin n))} = Set.pi Set.univ (fun _ => ({0} : Set ℝ)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      have := congrArg (fun y : EuclideanSpace ℝ (Fin n) => y i) h
      simpa using this
    · intro h
      ext i
      simpa using h i
  rw [hpre, Measure.pi_pi]
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, hn⟩)
  exact measure_singleton 0

open MeasureTheory ProbabilityTheory in
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere in
theorem p8ad8d14e_normalize_mem {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    BookProof.ChapterFreeFieldSphere.normalize x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  unfold BookProof.ChapterFreeFieldSphere.normalize
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

open BookProof.ChapterFreeFieldSphereSupport in
open MeasureTheory ProbabilityTheory in
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere in
theorem solution {n : ℕ} (hn : 0 < n) :
    sphereGaussian n (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = 1 := by
  unfold sphereGaussian
  rw [Measure.map_apply measurable_normalize Metric.isClosed_sphere.measurableSet]
  apply le_antisymm prob_le_one
  have hsub : ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set _) ⊆
      BookProof.ChapterFreeFieldSphere.normalize ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    fun x hx => p8ad8d14e_normalize_mem x hx
  calc (1 : ENNReal) = BookProof.ChapterFreeFieldGaussian.stdGaussian n ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ) := by
        rw [eq_comm, prob_compl_eq_one_iff (measurableSet_singleton _)]
        exact p8ad8d14e_stdGaussian_zero hn
    _ ≤ _ := measure_mono hsub
