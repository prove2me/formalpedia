-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_negative_tail_antitone_empty_of_eta_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:37:21.875646+00:00
-- url     : https://prove2.me/submissions/5b47d346-a6d9-44a8-aa65-0875dd52669c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (eta : ℕ → ℝ) (hpos : ∀ n, 0 < eta n)
    (hanti : Antitone eta)
    (hlim : Tendsto eta atTop (𝓝 (0 : ℝ))) :
    Antitone (fun n : ℕ => Ioo (-eta n) (0 : ℝ)) ∧
      (⋂ n : ℕ, Ioo (-eta n) (0 : ℝ)) = ∅ := by
  constructor
  · intro m n hmn z hz
    have hle : -eta m ≤ -eta n := neg_le_neg (hanti hmn)
    exact ⟨lt_of_le_of_lt hle hz.1, hz.2⟩
  · ext z
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hz
    have hzneg : z < 0 := (hz 0).2
    have hlimNeg : Tendsto (fun n : ℕ => -eta n) atTop (𝓝 (0 : ℝ)) := by
      simpa using hlim.neg
    have hEvent : ∀ᶠ n in atTop, z < -eta n :=
      hlimNeg.eventually (eventually_gt_nhds hzneg)
    obtain ⟨n, hn⟩ := hEvent.exists
    exact (lt_asymm (hz n).1 hn)

