-- Prove2me | solution 1 for BertsekasDP.admissible_cost_integrand_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T22:10:47.366247+00:00
-- url     : https://prove2.me/submissions/bd4b5e23-f104-428f-959f-bf3af4b1c5eb

import Definitions.Def_BertsekasCTModel

open Set Filter MeasureTheory
open scoped Topology Interval

-- These two fully proved helpers are reused from the accepted adjoint-existence proof.
private lemma integrable_of_bounded_continuous_off_finset
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → E) (F : Finset ℝ)
    (hv : ContinuousOn v (Icc a b \ (F : Set ℝ)))
    (hbdd : Bornology.IsBounded (v '' Icc a b)) :
    IntervalIntegrable v volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hm : AEStronglyMeasurable v (volume.restrict (Icc a b)) := by
    have h := hv.aestronglyMeasurable (μ := volume) (measurableSet_Icc.diff F.finite_toSet.measurableSet)
    rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self (F.finite_toSet.measure_zero volume))] at h
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  apply (integrable_const C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC (v t) (mem_image_of_mem v ht)

private lemma continuous_comp_piecewise_integrable
    {n m : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b)
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (hx : ContinuousOn x (Icc a b))
    (hu : BertsekasPiecewiseContinuousOn u (Icc a b))
    (φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → E)
    (hφ : Continuous φ) :
    IntervalIntegrable (fun t => φ (x t, u t)) volume a b := by
  obtain ⟨hbu, F, hcu⟩ := hu
  apply integrable_of_bounded_continuous_off_finset hab _ F
  · exact hφ.comp_continuousOn ((hx.mono sdiff_subset).prodMk hcu)
  · have hK := (isCompact_Icc.image_of_continuousOn hx).prod hbu.isCompact_closure
    apply (hK.image hφ).isBounded.subset
    rintro z ⟨t, ht, rfl⟩
    exact mem_image_of_mem φ ⟨mem_image_of_mem x ht, subset_closure (mem_image_of_mem u ht)⟩

theorem solution
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hg : Continuous (Function.uncurry M.g))
    (t₀ : ℝ) (ξ : EuclideanSpace ℝ (Fin n))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M t₀ ξ u x)
    (a b : ℝ) (ha : a ∈ Set.Icc t₀ M.T) (hb : b ∈ Set.Icc t₀ M.T) :
    IntervalIntegrable (fun t => M.g (x t) (u t)) MeasureTheory.volume a b := by
  have ht : t₀ ≤ M.T := ha.1.trans ha.2
  have hfull := continuous_comp_piecewise_integrable ht x u
    hadm.2.2.1 hadm.2.1 (Function.uncurry M.g) hg
  exact hfull.mono_set (uIcc_subset_uIcc
    (by simpa [uIcc_of_le ht] using ha)
    (by simpa [uIcc_of_le ht] using hb))
