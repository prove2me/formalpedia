-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_C2_of_C1_derivative_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:47:37.498991+00:00
-- url     : https://prove2.me/submissions/fcc0c42e-d429-42d5-adff-fd0a1d04e91c

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_volterra_integrated_identity_of_resolvent
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique
import Theorems.Thm_AvramDividend_Classical_causal_primitive_deriv_eq_continuous_on_positive
import Theorems.Thm_AvramDividend_Classical_contDiffOn_two_of_deriv_eq_C1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (K g V : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ContDiffOn ℝ 2 V (Ioi (0 : ℝ)) := by
  let G : ℝ → ℝ := fun x => ∫ s in Ioc (0 : ℝ) x, g s ∂volume
  obtain ⟨hGC1, hGb⟩ := causal_primitive_C1_locally_bounded g hg
  have hGe : ∀ x : ℝ, 0 < x →
      a * G x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * G s ∂volume) = x := by
    exact causal_volterra_integrated_identity_of_resolvent K g a β
      ha hK hg hgeq
  have hEq : ∀ x : ℝ, 0 < x → V x = G x :=
    causal_volterra_l1_continuous_solution_unique K a β ha hK V G
      hVc hGC1.continuousOn hVb hGb hVe hGe
  have hGdiff : DifferentiableOn ℝ G (Ioi (0 : ℝ)) := by
    exact (contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).1 hGC1 |>.1
  have hGderiv : ∀ x : ℝ, 0 < x → deriv G x = g x := by
    exact causal_primitive_deriv_eq_continuous_on_positive g hg
  have hGC2 : ContDiffOn ℝ 2 G (Ioi (0 : ℝ)) :=
    contDiffOn_two_of_deriv_eq_C1 G g hGdiff hgC1 hGderiv
  apply hGC2.congr
  intro x hx
  exact hEq x hx
