-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_endpoint_budget_of_prefix_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:23:02.364419+00:00
-- url     : https://prove2.me/submissions/a8a8de30-f2cd-474a-8ee1-a7eca6143055

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (σ : ℝ≥0∞) (S : ℝ≥0) (initial : ℝ)
    (K V R : ℝ≥0 → ℝ) (Kstop : ℝ) (hS : 0 < S)
    (hp : ∀ B : ℝ≥0, 0 < B → B ≤ S → (B : ℝ≥0∞) < σ →
      K B + V B ≤ initial + R B)
    (hc : 0 < σ → σ ≤ (S : ℝ≥0∞) →
      ∃ (u : ℕ → ℝ≥0) (l : ℝ),
        (∀ n, 0 < u n ∧ u n ≤ S ∧ (u n : ℝ≥0∞) < σ) ∧
        Tendsto (fun n => K (u n) + V (u n) - R (u n)) atTop (nhds l) ∧
        Kstop - R (min σ (S : ℝ≥0∞)).toNNReal ≤ l)
    (hz : σ = 0 → Kstop ≤ initial + R (min σ (S : ℝ≥0∞)).toNNReal)
    (hs : (S : ℝ≥0∞) < σ → Kstop = K S) :
    Kstop + (if (S : ℝ≥0∞) < σ then V S else 0) ≤
      initial + R (min σ (S : ℝ≥0∞)).toNNReal := by
  by_cases hsurv : (S : ℝ≥0∞) < σ
  · simpa only [hs hsurv, if_pos hsurv, min_eq_right (le_of_lt hsurv),
      ENNReal.toNNReal_coe] using hp S hS le_rfl hsurv
  · simp only [if_neg hsurv, add_zero]
    by_cases hr0 : σ = 0
    · exact hz hr0
    · obtain ⟨u, l, hu, hlim, hbound⟩ := hc
        (lt_of_le_of_ne (show (0 : ℝ≥0∞) ≤ σ from zero_le) (Ne.symm hr0)) (le_of_not_gt hsurv)
      have hl : l ≤ initial := le_of_tendsto hlim (Eventually.of_forall (fun n => by
        have hn := hp (u n) (hu n).1 (hu n).2.1 (hu n).2.2
        linarith))
      linarith
end
