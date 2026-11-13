-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB155_bounded_double_ae_L2_iterated_loss_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:23:51.103369+00:00
-- url     : https://prove2.me/submissions/66e12fe2-7ccd-4540-8ca2-41f842511b0d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB136_bounded_ae_product_L2_iterated_loss_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ℕ → α × β → ℝ) (g : α × β → ℝ)
    (hf : ∀ m, Measurable (f m)) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ m z, |f m z| ≤ B) (hgb : ∀ z, |g z| ≤ B)
    (hMeas : MeasurableSet {z : α × β |
      Tendsto (fun m : ℕ => f m z) atTop (𝓝 (g z))})
    (hae : ∀ᵐ b ∂ν, ∀ᵐ a ∂μ,
      Tendsto (fun m : ℕ => f m (a,b)) atTop (𝓝 (g (a,b)))) :
    Tendsto (fun m : ℕ =>
      ∫ a, (∫ b, (f m (a,b) - g (a,b)) ^ 2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hswap : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν,
      Tendsto (fun m : ℕ => f m (a,b)) atTop (𝓝 (g (a,b))) :=
    (Measure.ae_ae_comm hMeas).2 hae
  have hprod : ∀ᵐ z ∂(μ.prod ν),
      Tendsto (fun m : ℕ => f m z) atTop (𝓝 (g z)) :=
    (Measure.ae_prod_iff_ae_ae hMeas).2 hswap
  exact avram_gbB136_bounded_ae_product_L2_iterated_loss_tendsto
    μ ν f g hf hg B hB hfb hgb hprod
