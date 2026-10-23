-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_exponential_kernel_weight_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:31:58.312785+00:00
-- url     : https://prove2.me/submissions/1c738174-2fea-429c-876e-286e20d35f7a

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ weight : ℝ, 0 < weight ∧
      |β| / weight +
        (∫ t in Ioi (0 : ℝ),
          |K t| * Real.exp (-weight * t) ∂volume) < a := by
  have hnorm : Integrable (fun t : ℝ => |K t|)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using hK.norm
  have hkernel :
      Tendsto (fun n : ℕ =>
        ∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-(n : ℝ) * t) ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
    have hlim : Tendsto (fun n : ℕ =>
        ∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-(n : ℝ) * t) ∂volume)
        atTop (𝓝 (∫ t in Ioi (0 : ℝ), (0 : ℝ) ∂volume)) := by
      apply tendsto_integral_of_dominated_convergence (fun t : ℝ => |K t|)
      · intro n
        exact hnorm.aestronglyMeasurable.mul (by fun_prop)
      · exact hnorm
      · intro n
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hExp : Real.exp (-(n : ℝ) * t) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
          nlinarith [mul_nonneg hn ht.le]
        have hnonneg : 0 ≤ |K t| * Real.exp (-(n : ℝ) * t) :=
          mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact (mul_le_mul_of_nonneg_left hExp (abs_nonneg _)).trans_eq (mul_one _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htop : Tendsto (fun n : ℕ => (n : ℝ) * t) atTop atTop :=
          (tendsto_natCast_atTop_atTop).atTop_mul_const ht
        have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
        have hc : Tendsto (fun _ : ℕ => |K t|) atTop (𝓝 (|K t|)) :=
          tendsto_const_nhds
        simpa [neg_mul] using hc.mul he
    simpa using hlim
  have hdiv : Tendsto (fun n : ℕ => |β| / (n : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htotal : Tendsto (fun n : ℕ =>
      |β| / (n : ℝ) +
        (∫ t in Ioi (0 : ℝ),
          |K t| * Real.exp (-(n : ℝ) * t) ∂volume))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hdiv.add hkernel
  obtain ⟨n, hn, hsmall⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and
      (htotal.eventually (Iio_mem_nhds ha))).exists
  exact ⟨(n : ℝ), by exact_mod_cast hn, hsmall⟩