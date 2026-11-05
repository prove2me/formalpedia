-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:10:11.955046+00:00
-- url     : https://prove2.me/submissions/93dbe6e7-0d0b-4395-bfe0-b8486e0c0ca4

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hdetect : ∀ ω (s t : ℝ≥0), s < t →
      (x + X.X s ω - rightLimit D s ω < lower ∨
        upper < x + X.X s ω - rightLimit D s ω) →
      ∃ k, r k < t ∧
        (x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
          upper < x + X.X (r k) ω - rightLimit D (r k) ω)) :
    ∀ (ω : Ω) (T : ℝ≥0),
      (∀ t : ℝ≥0, t < T →
        lower ≤ x + X.X t ω - rightLimit D t ω ∧ x + X.X t ω - rightLimit D t ω ≤ upper) ↔
      (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨ upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) := by
  classical
  intro ω T
  constructor
  · intro hstay
    apply le_iInf
    intro k
    by_cases hex : x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨ upper < x + X.X (r k) ω - rightLimit D (r k) ω
    · have hnot : ¬ r k < T := by
        intro hrt
        obtain ⟨hl, hu⟩ := hstay (r k) hrt
        rcases hex with hlo | hup
        · exact (not_lt_of_ge hl) hlo
        · exact (not_lt_of_ge hu) hup
      have hr : T ≤ r k := le_of_not_gt hnot
      simpa only [if_pos hex] using (WithTop.coe_le_coe.mpr hr)
    · simpa only [if_neg hex] using
        (le_top : (T : WithTop ℝ≥0) ≤ (⊤ : WithTop ℝ≥0))
  · intro hstop t ht
    have hnexit : ¬ (x + X.X t ω - rightLimit D t ω < lower ∨ upper < x + X.X t ω - rightLimit D t ω) := by
      intro hex
      obtain ⟨k, hkT, hkE⟩ := hdetect ω t T ht hex
      have hk : (T : WithTop ℝ≥0) ≤
          (if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨ upper < x + X.X (r k) ω - rightLimit D (r k) ω
            then (r k : WithTop ℝ≥0) else ⊤) :=
        hstop.trans (iInf_le
          (fun k : ℕ => if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
              upper < x + X.X (r k) ω - rightLimit D (r k) ω
            then (r k : WithTop ℝ≥0) else ⊤) k)
      have hTk : T ≤ r k :=
        WithTop.coe_le_coe.mp (by simpa only [if_pos hkE] using hk)
      exact (not_le_of_gt hkT) hTk
    constructor
    · exact le_of_not_gt (fun h => hnexit (Or.inl h))
    · exact le_of_not_gt (fun h => hnexit (Or.inr h))