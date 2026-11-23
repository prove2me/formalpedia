-- Prove2me | solution 1 for AvramDividend.Classical.laplace_scaled_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:47:53.23395+00:00
-- url     : https://prove2.me/submissions/938672f9-4040-4d19-ade2-850496d6a340

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private theorem scaled_integral_impl
    (s : ℝ → ℝ) (βstar : ℝ) (hβstar : 0 < βstar)
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ s x)
    (hcont : ContinuousOn s (Set.Ici (0 : ℝ)))
    (hmono : MonotoneOn s (Set.Ici (0 : ℝ)))
    (hInt : IntegrableOn (fun x : ℝ => Real.exp (-βstar * x) * s x) (Set.Ioi 0) volume) :
    Tendsto (fun β : ℝ => ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * s (u / β)) atTop
      (𝓝 (s 0)) := by
  have hcomp0 : IntegrableOn
      (fun u : ℝ => Real.exp (-βstar * ((1 / βstar) * u)) * s ((1 / βstar) * u)) (Ioi 0) volume := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => Real.exp (-βstar * y) * s y) (0 : ℝ) (a := 1 / βstar)
      (one_div_pos.mpr hβstar)).2 (by simpa using hInt)
  have hcomp : IntegrableOn (fun u : ℝ => Real.exp (-u) * s (u / βstar)) (Ioi 0) volume := by
    simpa [div_eq_mul_inv, hβstar.ne', mul_comm, mul_left_comm, mul_assoc] using hcomp0
  have hDCT : Tendsto
      (fun β : ℝ => ∫ u in Ioi (0 : ℝ), Real.exp (-u) * s (u / β)) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), Real.exp (-u) * s 0)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (bound := fun u : ℝ => Real.exp (-u) * s (u / βstar))
    · filter_upwards [eventually_ge_atTop βstar] with β hβ
      have hβpos : 0 < β := hβstar.trans_le hβ
      have hqcont : ContinuousOn (fun u : ℝ => u / β) (Ioi (0 : ℝ)) := by fun_prop
      have hmaps : MapsTo (fun u : ℝ => u / β) (Ioi (0 : ℝ)) (Ici (0 : ℝ)) := by
        intro u hu
        exact div_nonneg hu.le hβpos.le
      have hsβ : ContinuousOn (fun u : ℝ => s (u / β)) (Ioi (0 : ℝ)) :=
        hcont.comp hqcont hmaps
      have heβ : ContinuousOn (fun u : ℝ => Real.exp (-u)) (Ioi (0 : ℝ)) := by fun_prop
      exact (heβ.mul hsβ).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [eventually_ge_atTop βstar] with β hβ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hβpos : 0 < β := hβstar.trans_le hβ
      have hu0 : 0 ≤ u := hu.le
      have huβ0 : 0 ≤ u / β := div_nonneg hu0 hβpos.le
      have huL0 : 0 ≤ u / βstar := div_nonneg hu0 hβstar.le
      have hdiv : u / β ≤ u / βstar := div_le_div_of_nonneg_left hu0 hβstar hβ
      have hsle : s (u / β) ≤ s (u / βstar) := hmono huβ0 huL0 hdiv
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (hnonneg _ huβ0)]
      exact mul_le_mul_of_nonneg_left hsle (Real.exp_pos _).le
    · exact hcomp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hquot : Tendsto (fun β : ℝ => u / β) atTop (𝓝 (0 : ℝ)) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hwithin : Tendsto (fun β : ℝ => u / β) atTop (𝓝[Ici (0 : ℝ)] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hquot ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
        exact div_nonneg hu.le hβ.le
      have hs_lim : Tendsto (fun β : ℝ => s (u / β)) atTop (𝓝 (s 0)) :=
        (hcont.continuousWithinAt (by simp)).tendsto.comp hwithin
      simpa using tendsto_const_nhds.mul hs_lim
  have hExpInt : (∫ u : ℝ in Ioi (0 : ℝ), Real.exp (-u)) = 1 := by
    have hh := integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) (0 : ℝ)
    simpa using hh
  have hconstInt : (∫ u in Ioi (0 : ℝ), Real.exp (-u) * s 0) = s 0 := by
    rw [integral_mul_const, hExpInt, one_mul]
  simpa [hconstInt] using hDCT

theorem solution
    (s : ℝ → ℝ) (βstar : ℝ) (hβstar : 0 < βstar)
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ s x)
    (hcont : ContinuousOn s (Set.Ici (0 : ℝ)))
    (hmono : MonotoneOn s (Set.Ici (0 : ℝ)))
    (hInt : IntegrableOn (fun x : ℝ => Real.exp (-βstar * x) * s x) (Set.Ioi 0) volume) :
    Tendsto (fun β : ℝ => ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * s (u / β)) atTop
      (𝓝 (s 0)) := by
  exact scaled_integral_impl s βstar hβstar hnonneg hcont hmono hInt
