-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_full_kernel_vanishes_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:48:39.987456+00:00
-- url     : https://prove2.me/submissions/c8e313b3-ffb9-4858-81c9-f9ae7764925c

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_vanishes_at_origin
import Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The constant drift and L1 convolution vanish at the positive-time origin. -/
theorem solution (K : ℝ → ℝ) (β w : ℝ)
    (f : BoundedContinuousFunction ℝ≥0 ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    Tendsto (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
      (β + K (x - s)) *
        (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by
  let V : ℝ → ℝ := fun s => Real.exp (w * s) *
    f ⟨max s 0, le_max_right s 0⟩
  have hVc : ContinuousOn V (Ici (0 : ℝ)) :=
    (causal_weighted_BCF_extension_continuous f w).continuousOn
  have hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C := by
    intro R hR
    exact causal_weighted_BCF_local_bound f w R hR
  have hK0 := causal_l1_convolution_vanishes_at_origin
    K V hK (hVc.mono (by intro s hs; change 0 < s at hs; exact le_of_lt hs)) hVb
  have hp : ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, V s ∂volume) (Ici (0 : ℝ)) :=
    causal_continuous_input_primitive_continuousOn_nonnegative V hVc
  have hp0 : Tendsto (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, V s ∂volume)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by
    have ht := hp.continuousWithinAt (by simp : (0 : ℝ) ∈ Ici (0 : ℝ))
    have hh := ht.mono_left
      (nhdsWithin_mono (0 : ℝ)
        (by intro x hx; change 0 < x at hx; exact le_of_lt hx : Ioi (0 : ℝ) ⊆ Ici 0))
    simpa using hh
  have hβ0 : Tendsto (fun x : ℝ =>
      β * (∫ s in Ioc (0 : ℝ) x, V s ∂volume))
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hp0)
  have hsum : Tendsto (fun x : ℝ =>
      β * (∫ s in Ioc (0 : ℝ) x, V s ∂volume) +
      (∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume))
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by
    simpa using hβ0.add hK0
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hv : IntegrableOn V (Ioc (0 : ℝ) x) volume := by
    have hi : ContinuousOn V (Icc (0 : ℝ) x) :=
      hVc.mono (by intro s hs; exact hs.1)
    exact hi.integrableOn_Icc.mono_set
      (by intro s hs; exact ⟨le_of_lt hs.1, hs.2⟩)
  have hki := causal_l1_kernel_continuous_input_integrable K V hK hVc x hx
  calc
    β * (∫ s in Ioc (0 : ℝ) x, V s ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume) =
        (∫ s in Ioc (0 : ℝ) x, β * V s ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume) := by
          rw [integral_const_mul]
    _ = (∫ s in Ioc (0 : ℝ) x,
          β * V s + K (x - s) * V s ∂volume) :=
      (integral_add (hv.const_mul β) hki).symm
    _ = (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) := by
      apply integral_congr_ae
      filter_upwards [] with s
      ring