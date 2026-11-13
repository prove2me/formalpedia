-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_finite_product_ae_bounded_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:36:13.831364+00:00
-- url     : https://prove2.me/submissions/fc14dfb3-8457-4ccc-aa10-40d2bc974181

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (hμ : μ Set.univ < ⊤) (hν : ν Set.univ < ⊤)
    (H : α × β → ℝ)
    (hHm : AEStronglyMeasurable H (μ.prod ν))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ᵐ p ∂(μ.prod ν), |H p| ≤ K) :
    Integrable H (μ.prod ν) := by
  haveI : IsFiniteMeasure μ := ⟨hμ⟩
  haveI : IsFiniteMeasure ν := ⟨hν⟩
  haveI : IsFiniteMeasure (μ.prod ν) := inferInstance
  have hConst : Integrable (fun _ : α × β => K) (μ.prod ν) :=
    integrable_const K
  apply hConst.mono' hHm
  filter_upwards [hK] with p hp
  simpa only [Real.norm_eq_abs] using hp
