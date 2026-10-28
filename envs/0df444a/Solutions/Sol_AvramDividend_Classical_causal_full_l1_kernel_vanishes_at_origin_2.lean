-- Prove2me | solution 2 for AvramDividend.Classical.causal_full_l1_kernel_vanishes_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:10:35.402428+00:00
-- url     : https://prove2.me/submissions/cfe40098-5536-4fcd-9498-40041c0da140

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_vanishes_at_origin
import Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
theorem solution
    (K V : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ici (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    Tendsto (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
      (β + K (x - s)) * V s ∂volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 := AvramDividend.Classical.causal_l1_convolution_vanishes_at_origin K V hK
    (hVc.mono Ioi_subset_Ici_self) hVb
  have hP := AvramDividend.Classical.causal_continuous_input_primitive_continuousOn_nonnegative V hVc
  have h2 : Tendsto (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, V s ∂volume) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((hP 0 (le_refl (0:ℝ))).mono Ioi_subset_Ici_self).tendsto
    simpa using this
  have := (h2.const_mul β).add h1
  rw [mul_zero, zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  have hVi : IntegrableOn V (Ioc (0 : ℝ) x) volume :=
    ((hVc.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hKi := AvramDividend.Classical.causal_l1_kernel_continuous_input_integrable K V hK hVc x hx
  simp_rw [add_mul]
  rw [integral_add (hVi.const_mul β) hKi, integral_const_mul]
