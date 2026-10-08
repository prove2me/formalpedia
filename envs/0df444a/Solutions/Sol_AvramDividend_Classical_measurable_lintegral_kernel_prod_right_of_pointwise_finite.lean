-- Prove2me | solution 1 for AvramDividend.Classical.measurable_lintegral_kernel_prod_right_of_pointwise_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:19:56.791173+00:00
-- url     : https://prove2.me/submissions/4f2da910-a279-426e-be66-b30d485ee435

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped MeasureTheory ENNReal Topology

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β)
    (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a, b) ∂(κ a)) := by
  let F : ℕ → SimpleFunc (α × β) ℝ≥0∞ := SimpleFunc.eapprox f
  have h : ∀ p, ⨆ n, F n p = f p :=
    SimpleFunc.iSup_eapprox_apply hf
  simp_rw [← h]
  have hint :
      ∀ a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) =
        ⨆ n, ∫⁻ b, F n (a, b) ∂κ a := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox f hij _
  simp_rw [hint]
  refine .iSup fun n => ?_
  refine SimpleFunc.induction
    (motive := fun g =>
      Measurable (fun (a : α) => ∫⁻ (b : β), g (a, b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise,
      SimpleFunc.coe_const, SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    unfold Function.const
    simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
    exact Measurable.const_mul
      (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite
        (κ := κ) ht hκ) c
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have h_add :
        (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
          (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) +
            fun a => ∫⁻ b, g₂ (a, b) ∂κ a := by
      ext a
      rw [Pi.add_apply, lintegral_add_left (by fun_prop)]
    rw [h_add]
    exact Measurable.add hm₁ hm₂
