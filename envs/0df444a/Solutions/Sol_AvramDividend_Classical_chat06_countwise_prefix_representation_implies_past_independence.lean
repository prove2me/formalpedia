-- Prove2me | solution 1 for AvramDividend.Classical.chat06_countwise_prefix_representation_implies_past_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:07:42.92846+00:00
-- url     : https://prove2.me/submissions/f05700a8-eff3-4fbd-a505-7af83c9811e8

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_chat06_selected_past_residual_future_joint_countwise_gluing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The complete observed-past factorisation follows when every
past event, restricted to a count cylinder, has a measurable
representation through the corresponding earlier-arrival prefix.
This isolates the genuine natural-filtration representation obligation. -/
theorem solution
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace A]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (Z : ℕ → Ω → A)
    (H : Set Ω) (hH : MeasurableSet H)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n))
    (G : ℕ → Ω → E) (hG : ∀ n, Measurable (G n))
    (B : Set E) (hB : MeasurableSet B)
    (u : ℝ) (c d : ℝ≥0∞)
    (hRep : ∀ n : ℕ, ∃ Q : Set A,
      MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω = n) =ᵐ[P]
        (fun ω : Ω => Z n ω ∈ Q ∧ N ω = n))
    (hPrefixFactor : ∀ n (Q : Set A), MeasurableSet Q →
      P {ω | Z n ω ∈ Q ∧ N ω = n ∧
        u < F n ω ∧ G n ω ∈ B} =
        (P {ω | Z n ω ∈ Q ∧ N ω = n} * c) * d) :
    P {ω | ω ∈ H ∧ u < F (N ω) ω ∧
      G (N ω) ω ∈ B} = (P H * c) * d := by
  apply AvramDividend.Classical.chat06_selected_past_residual_future_joint_countwise_gluing
    N hN H hH F hF G hG B hB u c d
  intro n
  obtain ⟨Q, hQ, hRepN⟩ := hRep n
  have hJointAE :
      (fun ω : Ω => ω ∈ H ∧ N ω = n ∧
        u < F n ω ∧ G n ω ∈ B) =ᵐ[P]
      (fun ω : Ω => Z n ω ∈ Q ∧ N ω = n ∧
        u < F n ω ∧ G n ω ∈ B) := by
    filter_upwards [hRepN] with ω hω
    apply propext
    constructor
    · rintro ⟨hh, hn, hu, hb⟩
      obtain ⟨hq, hn'⟩ := (Iff.of_eq hω).mp ⟨hh, hn⟩
      exact ⟨hq, hn', hu, hb⟩
    · rintro ⟨hq, hn, hu, hb⟩
      obtain ⟨hh, hn'⟩ := (Iff.of_eq hω).mpr ⟨hq, hn⟩
      exact ⟨hh, hn', hu, hb⟩
  have hBase :
      P {ω | ω ∈ H ∧ N ω = n} =
        P {ω | Z n ω ∈ Q ∧ N ω = n} :=
    measure_congr hRepN
  calc
    P {ω | ω ∈ H ∧ N ω = n ∧
      u < F n ω ∧ G n ω ∈ B} =
      P {ω | Z n ω ∈ Q ∧ N ω = n ∧
        u < F n ω ∧ G n ω ∈ B} :=
      measure_congr hJointAE
    _ = (P {ω | Z n ω ∈ Q ∧ N ω = n} * c) * d :=
      hPrefixFactor n Q hQ
    _ = (P {ω | ω ∈ H ∧ N ω = n} * c) * d := by
      rw [hBase]
