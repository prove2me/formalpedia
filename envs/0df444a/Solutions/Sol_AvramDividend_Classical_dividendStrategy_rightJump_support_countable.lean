-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_rightJump_support_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:12:36.978114+00:00
-- url     : https://prove2.me/submissions/a555942f-7fcb-4e90-a5cc-5e9b7272f751

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_monotone_rightJump_support_countable
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Countable {t : ℝ | 0 ≤ t ∧
      rightLimit D t.toNNReal ω ≠ D t.toNNReal ω} := by
  have hmono : Monotone (fun s : ℝ => D s.toNNReal ω) := by
    intro a b hab
    exact (hD.2.1 ω) (Real.toNNReal_mono hab)
  refine (monotone_rightJump_support_countable
    (fun s : ℝ => D s.toNNReal ω) hmono).mono ?_
  intro t ht
  obtain ⟨ht0, htjump⟩ := ht
  have heq : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht0
  have hlim :=
    dividendPath_real_rightLim_eq_rightLimit D ω (hD.2.1 ω) t.toNNReal
  rw [heq] at hlim
  change Function.rightLim (fun s : ℝ => D s.toNNReal ω) t ≠
    D t.toNNReal ω
  rw [hlim]
  exact htjump
