-- Prove2me | solution 1 for ChanceStateCtrl.General.theorem_2_2_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T01:20:29.746378+00:00
-- url     : https://prove2.me/submissions/6b2e7e56-9b24-4af7-9f84-9f3a0bb1800a

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
import Theorems.Thm_ChanceStateCtrl_General_eq_14_spherical_radial
import Theorems.Thm_ChanceStateCtrl_General_theorem_2_2_e_lipschitz_bounded
import Theorems.Thm_ChanceStateCtrl_General_theorem_2_2_e_lipschitz_moderate
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

open ChanceStateCtrl.General

theorem solution {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (ub : U) (h10 : g ub 0 < 0)
    (h12 : ModerateGrowth g Sigma ub ∨ Bornology.IsBounded {z | g ub z ≤ 0}) :
    (∃ K : NNReal, ∃ t ∈ 𝓝 ub, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        LipschitzOnWith K (fun u => radialProb Sigma g u v) t) ∧
      LocLipAt (probFn P ξ g) ub := by
  classical
  have hE : ∃ K : NNReal, ∃ t ∈ 𝓝 ub, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      LipschitzOnWith K (fun u => radialProb Sigma g u v) t :=
    h12.elim (fun h => theorem_2_2_e_lipschitz_moderate P ξ Sigma g hA ub h10 h)
      (fun h => theorem_2_2_e_lipschitz_bounded P ξ Sigma g hA ub h10 h)
  refine ⟨hE, ?_⟩
  obtain ⟨K, t, ht, hK⟩ := hE
  have h14 := eq_14_spherical_radial P ξ Sigma g hA
  -- the chi law is a finite measure
  have hchi_int : Integrable (chiDensity m) := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ ((m - 1 : ℕ) : ℝ) * Real.exp (-(1 / 2) * x ^ 2))
        (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by
        have : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith)
    have h2 : IntegrableOn (fun x : ℝ => chiConst m * x ^ (m - 1) * Real.exp (-x ^ 2 / 2))
        (Set.Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      refine IntegrableOn.congr_fun (Integrable.const_mul h1 (chiConst m)) (fun x hx => ?_) measurableSet_Ioi
      rw [Real.rpow_natCast, mul_assoc]
      congr 3; ring
    have h3 : chiDensity m = (Set.Ici (0 : ℝ)).indicator
        (fun x : ℝ => chiConst m * x ^ (m - 1) * Real.exp (-x ^ 2 / 2)) := by
      funext x
      simp only [chiDensity, Set.indicator, Set.mem_Ici]
    rw [h3]
    exact (integrable_indicator_iff measurableSet_Ici).2 h2
  have hchi_meas : Measurable (chiDensity m) := by
    unfold chiDensity
    exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
  haveI : IsFiniteMeasure (chiLaw m) := by
    refine ⟨?_⟩
    rw [chiLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hnn : ∀ x, 0 ≤ chiDensity m x := by
      intro x; unfold chiDensity
      split_ifs with h
      · have : 0 ≤ chiConst m := by
          unfold chiConst
          exact inv_nonneg.2 (setIntegral_nonneg measurableSet_Ioi fun x hx =>
            mul_nonneg (pow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le)
        positivity
      · exact le_rfl
    exact lt_top_iff_ne_top.2 ((lintegral_ofReal_ne_top_iff_integrable
      hchi_meas.aestronglyMeasurable (Eventually.of_forall hnn)).2 hchi_int)
  -- the sphere law is a probability measure
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) ≠ 0 := by
    simp only [finrank_euclideanSpace_fin]; exact hA.dim_pos.ne'
  have hS0 : (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere Set.univ ≠ 0 := by
    intro h
    have := (Measure.toSphere_eq_zero_iff_finrank (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))).1
      (Measure.measure_univ_eq_zero.1 h)
    exact hdim this
  haveI : IsProbabilityMeasure (sphereLaw m) := by
    refine ⟨?_⟩
    rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hS0 (measure_ne_top _ _)
  -- measurability and boundedness of `e(u, ·)`
  have hmeas : ∀ u, Measurable (fun v => radialProb Sigma g u v) := by
    intro u
    set S : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × ℝ) :=
      {q | 0 ≤ q.2 ∧ g u (q.2 • sqrtCov Sigma (q.1 : EuclideanSpace ℝ (Fin m))) ≤ 0} with hSdef
    have hgu : Continuous (g u) :=
      hA.locLip.continuous.comp (Continuous.prodMk continuous_const continuous_id)
    have hS : MeasurableSet S := by
      apply IsClosed.measurableSet
      apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
      exact isClosed_le (hgu.comp (continuous_snd.smul
        ((sqrtCov Sigma).continuous.comp (continuous_subtype_val.comp continuous_fst))))
        continuous_const
    exact (measurable_measure_prodMk_left (ν := chiLaw m) hS).ennreal_toReal
  have hbdd : ∀ u v, ‖radialProb Sigma g u v‖ ≤ (chiLaw m Set.univ).toReal := by
    intro u v
    rw [Real.norm_eq_abs, radialProb, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
  have hint : ∀ u, Integrable (fun v => radialProb Sigma g u v) (sphereLaw m) := fun u =>
    Integrable.of_bound (hmeas u).aestronglyMeasurable _ (Eventually.of_forall (hbdd u))
  refine ⟨K, t, ht, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [h14 x, h14 y, dist_eq_norm, ← integral_sub (hint x) (hint y)]
  have := norm_integral_le_of_norm_le_const (μ := sphereLaw m)
    (f := fun v => radialProb Sigma g x v - radialProb Sigma g y v) (C := K * dist x y)
    (Eventually.of_forall fun v => by
      rw [← dist_eq_norm]; exact (hK v).dist_le_mul x hx y hy)
  rwa [probReal_univ, mul_one] at this
