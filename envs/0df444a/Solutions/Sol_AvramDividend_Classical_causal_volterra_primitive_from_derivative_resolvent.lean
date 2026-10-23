-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_primitive_from_derivative_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:02:18.129033+00:00
-- url     : https://prove2.me/submissions/ec75839a-d562-41c2-ac66-6c8cb6af68ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_volterra_integrated_identity_of_resolvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ∃ G : ℝ → ℝ,
      ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) := by
  let G : ℝ → ℝ := fun x => ∫ s in Ioc (0 : ℝ) x, g s ∂volume
  obtain ⟨hC1, hBound⟩ :=
    AvramDividend.Classical.causal_primitive_C1_locally_bounded g hg
  refine ⟨G, hC1, hBound, ?_⟩
  intro x hx
  exact AvramDividend.Classical.causal_volterra_integrated_identity_of_resolvent
    K g a β ha hK hg hgeq x hx
