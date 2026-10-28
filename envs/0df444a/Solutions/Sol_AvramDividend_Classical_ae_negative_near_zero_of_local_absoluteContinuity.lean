-- Prove2me | solution 1 for AvramDividend.Classical.ae_negative_near_zero_of_local_absoluteContinuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:00:36.591588+00:00
-- url     : https://prove2.me/submissions/8f19b57a-b6ba-4b5f-9814-b854b72136a1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (P Q : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (horizons : ℕ → ℝ≥0)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hEvent : ∀ n : ℕ,
      MeasurableSet[𝓕 (horizons n)]
        {ω : Ω | ∃ s : ℝ≥0,
          s < horizons n ∧ X s ω < 0})
    (hLocalAC : ∀ n : ℕ, ∀ A : Set Ω,
      MeasurableSet[𝓕 (horizons n)] A →
        P A = 0 → Q A = 0)
    (hRegP : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X s ω < 0) :
    ∀ᵐ ω ∂Q, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X s ω < 0 := by
  have hEach : ∀ n : ℕ, ∀ᵐ ω ∂Q,
      ∃ s : ℝ≥0, s < horizons n ∧ X s ω < 0 := by
    intro n
    have hP : ∀ᵐ ω ∂P,
        ∃ s : ℝ≥0, s < horizons n ∧ X s ω < 0 := by
      filter_upwards [hRegP] with ω hω
      exact hω (horizons n) (hpos n)
    have hBadMeas :
        MeasurableSet[𝓕 (horizons n)]
          {ω : Ω | ¬ ∃ s : ℝ≥0,
            s < horizons n ∧ X s ω < 0} := by
      simpa only [Set.compl_setOf] using (hEvent n).compl
    have hBadP :
        P {ω : Ω | ¬ ∃ s : ℝ≥0,
            s < horizons n ∧ X s ω < 0} = 0 :=
      ae_iff.mp hP
    exact (ae_iff).2 (hLocalAC n _ hBadMeas hBadP)
  have hAll : ∀ᵐ ω ∂Q, ∀ n : ℕ,
      ∃ s : ℝ≥0, s < horizons n ∧ X s ω < 0 :=
    (ae_all_iff).2 hEach
  filter_upwards [hAll] with ω hω ε hε
  obtain ⟨n, hn⟩ := hcofinal ε hε
  obtain ⟨s, hs, hneg⟩ := hω n
  exact ⟨s, lt_of_lt_of_le hs hn, hneg⟩
