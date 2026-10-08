-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:07:44.838969+00:00
-- url     : https://prove2.me/submissions/66119c6b-6bda-4507-a059-60278315decf

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
theorem p4a9d5f37_stdGaussian_zero {n : ℕ} (hn : 0 < n) :
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

theorem p4a9d5f37_normalize_mem {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    BookProof.ChapterFreeFieldSphere.normalize x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  unfold BookProof.ChapterFreeFieldSphere.normalize
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

open MeasureTheory ProbabilityTheory in
theorem p4a9d5f37_sphere {n : ℕ} (hn : 0 < n) :
    BookProof.ChapterFreeFieldSphere.sphereGaussian n
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = 1 := by
  unfold BookProof.ChapterFreeFieldSphere.sphereGaussian
  rw [Measure.map_apply BookProof.ChapterFreeFieldSphere.measurable_normalize
    Metric.isClosed_sphere.measurableSet]
  apply le_antisymm prob_le_one
  have hsub : ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set _) ⊆
      BookProof.ChapterFreeFieldSphere.normalize ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    fun x hx => p4a9d5f37_normalize_mem x hx
  calc (1 : ENNReal) = BookProof.ChapterFreeFieldGaussian.stdGaussian n
        ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ) := by
        rw [eq_comm, prob_compl_eq_one_iff (measurableSet_singleton _)]
        exact p4a9d5f37_stdGaussian_zero hn
    _ ≤ _ := measure_mono hsub

theorem p4a9d5f37_born_mem {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    BookProof.ChapterFreeFieldBorn.bornMap x ∈ stdSimplex ℝ (Fin n) := by
  rw [mem_sphere_zero_iff_norm] at hx
  refine ⟨fun k => sq_nonneg _, ?_⟩
  have h := EuclideanSpace.norm_sq_eq x
  rw [hx] at h
  unfold BookProof.ChapterFreeFieldBorn.bornMap
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [← h]; norm_num

theorem p4a9d5f37_measurable_born {n : ℕ} :
    Measurable (BookProof.ChapterFreeFieldBorn.bornMap : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) := by
  unfold BookProof.ChapterFreeFieldBorn.bornMap
  apply Continuous.measurable
  fun_prop

open BookProof.ChapterFreeFieldBorn MeasureTheory BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere BookProof.ChapterFreeFieldSphereSupport in
theorem solution {n : ℕ} (hn : 0 < n) :
    ((sphereGaussian n).map bornMap) (stdSimplex ℝ (Fin n)) = 1 := by
  rw [Measure.map_apply p4a9d5f37_measurable_born (isClosed_stdSimplex ℝ (Fin n)).measurableSet]
  apply le_antisymm prob_le_one
  rw [← p4a9d5f37_sphere hn]
  exact measure_mono (fun x hx => p4a9d5f37_born_mem x hx)
