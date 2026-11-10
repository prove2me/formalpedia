-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose17_original_exit_inf_nearby_violation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:41:42.125864+00:00
-- url     : https://prove2.me/submissions/11619063-0f5f-43bf-aadd-035042762031

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A finite infimum of actual original sampled threshold violations is
approached by true violating observation times from the right. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (r : ℕ → ℝ≥0) (δ : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) =
      ⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ k : ℕ, t ≤ r k ∧ r k < t + ε ∧
        x + X.X (r k) ω - rightLimit D (r k) ω < δ := by
  classical
  intro ε hε
  by_contra hno
  have hbound (k : ℕ) :
      (↑(t + ε) : WithTop ℝ≥0) ≤
        (if x + X.X (r k) ω - rightLimit D (r k) ω < δ
          then (r k : WithTop ℝ≥0) else ⊤) := by
    by_contra h
    have hlt : (if x + X.X (r k) ω - rightLimit D (r k) ω < δ
          then (r k : WithTop ℝ≥0) else ⊤) <
        (↑(t + ε) : WithTop ℝ≥0) := lt_of_not_ge h
    by_cases hk : x + X.X (r k) ω - rightLimit D (r k) ω < δ
    · have htk : (t : WithTop ℝ≥0) ≤
          (if x + X.X (r k) ω - rightLimit D (r k) ω < δ
            then (r k : WithTop ℝ≥0) else ⊤) := by
        rw [ht]
        exact iInf_le _ k
      have hleft : t ≤ r k :=
        WithTop.coe_le_coe.mp (by simpa [hk] using htk)
      have hright : r k < t + ε :=
        WithTop.coe_lt_coe.mp (by simpa [hk] using hlt)
      exact hno ⟨k, hleft, hright, hk⟩
    · simp [hk] at hlt
  have hle : (↑(t + ε) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
    rw [ht]
    exact le_iInf (fun k => hbound k)
  have hreal : t + ε ≤ t := WithTop.coe_le_coe.mp hle
  exact (not_le_of_gt (lt_add_of_pos_right t hε)) hreal
