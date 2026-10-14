-- Prove2me | solution 1 for DbarRegularity.convolution_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:31:46.056736+00:00
-- url     : https://prove2.me/submissions/deaf426c-6723-45f9-bc9a-20e78cc9bc4e

import Mathlib.Analysis.Fourier.LpSpace
import Theorems.Thm_DbarRegularity_eLpNorm_conv_le_of_integrable
import Theorems.Thm_DbarRegularity_integrable_mul_sub_of_memLp_two
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Mathlib.MeasureTheory.Function.LpSpace.Complete



namespace DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

/-- **`L²` bound.** If `K ∈ L²(ℝ^d)` has `L²` Fourier transform bounded by `B`, then
`f ↦ ∫ K(· - y) f(y) dy` maps `L²` to `L²` with norm at most `B`. -/
theorem convolution_l2_bound {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume) (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : MemLp f 2 volume) :
    MemLp (fun x => ∫ y, K (x - y) * f y) 2 volume ∧
      eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume := by
  have hbound : eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤
      ENNReal.ofReal B * eLpNorm f 2 volume := by
    set fn : ℕ → EuclideanSpace ℝ (Fin d) → ℂ :=
      fun n => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) n).indicator f with hfn
    have hfn2 : ∀ n, MemLp (fn n) 2 volume := fun n => hf.indicator measurableSet_closedBall
    have hfn1 : ∀ n, Integrable (fn n) volume := by
      intro n
      haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) n)) :=
        isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
      exact (integrable_indicator_iff measurableSet_closedBall).2
        ((hf.restrict _).integrable one_le_two)
    have hlim : ∀ x, Tendsto (fun n => ∫ y, K (x - y) * fn n y) atTop
        (𝓝 (∫ y, K (x - y) * f y)) := by
      intro x
      refine tendsto_integral_of_dominated_convergence (fun y => ‖K (x - y) * f y‖)
        (fun n => (integrable_mul_sub_of_memLp_two hK (hfn2 n) x).1)
        (integrable_mul_sub_of_memLp_two hK hf x).norm (fun n => ae_of_all _ fun y => ?_)
        (ae_of_all _ fun y => ?_)
      · simp only [hfn, norm_mul]
        gcongr
        exact norm_indicator_le_norm_self _ _
      · refine (tendsto_const_nhds (x := K (x - y) * f y)).congr' ?_
        filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
        simp only [hfn]
        rw [Set.indicator_of_mem]
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
      (fun n => aestronglyMeasurable_integral_mul_sub K (fn n) hK.1 (hfn2 n).1) _
      (ae_of_all _ hlim)).trans ?_
    refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    calc eLpNorm (fun x => ∫ y, K (x - y) * fn n y) 2 volume
        ≤ ENNReal.ofReal B * eLpNorm (fn n) 2 volume :=
          eLpNorm_conv_le_of_integrable K hK B hB (fn n) (hfn1 n) (hfn2 n)
      _ ≤ ENNReal.ofReal B * eLpNorm f 2 volume := by
          gcongr; exact eLpNorm_indicator_le _
  exact ⟨⟨aestronglyMeasurable_integral_mul_sub K f hK.1 hf.1,
    hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)⟩, hbound⟩

end DbarRegularity

open DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

theorem solution {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume) (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : MemLp f 2 volume) :
    MemLp (fun x => ∫ y, K (x - y) * f y) 2 volume ∧
      eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume :=
  convolution_l2_bound K hK B hB f hf
