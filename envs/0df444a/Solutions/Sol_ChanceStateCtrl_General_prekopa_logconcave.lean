-- Prove2me | solution 1 for ChanceStateCtrl.General.prekopa_logconcave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T01:12:15.546998+00:00
-- url     : https://prove2.me/submissions/1b821f57-4450-48bb-a249-a4fc0849cd99

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Theorems.Thm_ConvexOptimization_prekopa_leindler
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

open ChanceStateCtrl.General

theorem solution {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U]
    [NormedSpace ℝ U] {m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (dens : EuclideanSpace ℝ (Fin m) → ℝ) (hdens_nonneg : ∀ z, 0 ≤ dens z)
    (hdens_meas : Measurable dens)
    (hlaw : P.map ξ = volume.withDensity (fun z => ENNReal.ofReal (dens z)))
    (hdens_logconcave : ∀ z w : EuclideanSpace ℝ (Fin m), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dens z ^ t * dens w ^ (1 - t) ≤ dens (t • z + (1 - t) • w))
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hg_lip : LocallyLipschitz (Function.uncurry g))
    (hg_qc : QuasiconvexOn ℝ Set.univ (Function.uncurry g)) :
    ∀ u w : U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      probFn P ξ g u ^ t * probFn P ξ g w ^ (1 - t) ≤ probFn P ξ g (t • u + (1 - t) • w) := by
  classical
  set C : U → Set (EuclideanSpace ℝ (Fin m)) := fun u => {z | g u z ≤ 0} with hCdef
  have hgc : Continuous (Function.uncurry g) := hg_lip.continuous
  have hCmeas : ∀ u, MeasurableSet (C u) := fun u =>
    (isClosed_le (hgc.comp (Continuous.prodMk continuous_const continuous_id))
      continuous_const).measurableSet
  have hint : Integrable dens := by
    have h1 : ∫⁻ z, ENNReal.ofReal (dens z) = 1 := by
      have := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin m)) => μ Set.univ) hlaw
      rw [Measure.map_apply hξ MeasurableSet.univ, Set.preimage_univ, measure_univ,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      exact this.symm
    exact (lintegral_ofReal_ne_top_iff_integrable hdens_meas.aestronglyMeasurable
      (Eventually.of_forall hdens_nonneg)).1 (by rw [h1]; exact ENNReal.one_ne_top)
  have hφ : ∀ u, probFn P ξ g u = ∫ z, (C u).indicator dens z := by
    intro u
    unfold probFn
    have hpre : {ω | g u (ξ ω) ≤ 0} = ξ ⁻¹' (C u) := rfl
    rw [hpre, ← Measure.map_apply hξ (hCmeas u), hlaw, withDensity_apply _ (hCmeas u),
      integral_indicator (hCmeas u), ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
        (Eventually.of_forall hdens_nonneg), ENNReal.toReal_ofReal
        (setIntegral_nonneg (hCmeas u) fun z _ => hdens_nonneg z)]
  intro u w t ht
  rcases ht.1.eq_or_lt with h0 | h0
  · subst h0; simp
  rcases ht.2.eq_or_lt with h1 | h1
  · subst h1; simp
  set F : U → EuclideanSpace ℝ (Fin m) → ENNReal :=
    fun v z => ENNReal.ofReal ((C v).indicator dens z) with hFdef
  have hind0 : ∀ v x, 0 ≤ (C v).indicator dens x := fun v x =>
    Set.indicator_nonneg (fun z _ => hdens_nonneg z) x
  have hFm : ∀ v, Measurable (F v) := fun v =>
    ENNReal.measurable_ofReal.comp (hdens_meas.indicator (hCmeas v))
  have hlin : ∀ v, ∫⁻ z, F v z = ENNReal.ofReal (probFn P ξ g v) := by
    intro v
    rw [hφ v, ofReal_integral_eq_lintegral_ofReal (hint.indicator (hCmeas v))
      (Eventually.of_forall (hind0 v))]
  have hφ0 : ∀ v, 0 ≤ probFn P ξ g v := fun v => ENNReal.toReal_nonneg
  have key := ConvexOptimization.prekopa_leindler (1 - t) (by linarith) (by linarith)
    (F u) (F w) (F (t • u + (1 - t) • w)) (hFm u) (hFm w) (hFm _) (by
      intro x y
      rw [show 1 - (1 - t) = t by ring]
      simp only [hFdef]
      rw [ENNReal.ofReal_rpow_of_nonneg (hind0 u x) ht.1,
        ENNReal.ofReal_rpow_of_nonneg (hind0 w y) (by linarith),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hind0 u x) _)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hx : x ∈ C u
      · by_cases hy : y ∈ C w
        · have hconv := hg_qc 0
          have hmem := hconv ⟨Set.mem_univ (u, x), hx⟩ ⟨Set.mem_univ (w, y), hy⟩ ht.1
            (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
          have hz : t • x + (1 - t) • y ∈ C (t • u + (1 - t) • w) := by
            have := hmem.2
            simp only [Prod.smul_mk, Prod.mk_add_mk, Function.uncurry_apply_pair] at this
            exact this
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
          exact hdens_logconcave x y t ht
        · rw [Set.indicator_of_notMem hy, Real.zero_rpow (by linarith), mul_zero]
          exact hind0 _ _
      · rw [Set.indicator_of_notMem hx, Real.zero_rpow h0.ne', zero_mul]
        exact hind0 _ _)
  rw [show 1 - (1 - t) = t by ring, hlin, hlin, hlin,
    ENNReal.ofReal_rpow_of_nonneg (hφ0 u) ht.1,
    ENNReal.ofReal_rpow_of_nonneg (hφ0 w) (by linarith),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hφ0 u) _)] at key
  exact (ENNReal.ofReal_le_ofReal_iff (hφ0 _)).1 key
