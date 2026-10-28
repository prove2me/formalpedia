-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_deriv_eq_resolvent_on_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:59:43.961966+00:00
-- url     : https://prove2.me/submissions/5089dec5-545c-40e1-b648-a07e85ca70a5

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_volterra_integrated_identity_of_resolvent
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique
import Theorems.Thm_AvramDividend_Classical_causal_primitive_deriv_eq_continuous_on_positive
open AvramDividend.Classical MeasureTheory Set Filter
theorem solution
    (K g V : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ∀ x : ℝ, 0 < x → deriv V x = g x := by
  obtain ⟨hC1, hGb⟩ := AvramDividend.Classical.causal_primitive_C1_locally_bounded g hg
  have hVG := AvramDividend.Classical.causal_volterra_l1_continuous_solution_unique K a β ha hK V
    (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, g s ∂volume) hVc hC1.continuousOn hVb hGb hVe
    (AvramDividend.Classical.causal_volterra_integrated_identity_of_resolvent K g a β ha hK hg hgeq)
  intro x hx
  have heq : V =ᶠ[nhds x] (fun y : ℝ => ∫ s in Ioc (0 : ℝ) y, g s ∂volume) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hVG y hy
  rw [heq.deriv_eq]
  exact AvramDividend.Classical.causal_primitive_deriv_eq_continuous_on_positive g hg x hx
