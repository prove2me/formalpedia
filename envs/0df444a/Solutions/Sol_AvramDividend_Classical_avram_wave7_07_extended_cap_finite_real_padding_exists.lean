-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_extended_cap_finite_real_padding_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:42:55.183579+00:00
-- url     : https://prove2.me/submissions/5a02755f-f34b-42d8-a247-3835270812e1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A positive finite real interior point of an extended cap admits a
    larger finite real localisation cutoff still strictly under the cap. -/
theorem solution
    (C : ℝ≥0∞) (v : ℝ) (hv0 : 0 ≤ v)
    (hv : ENNReal.ofReal v < C) :
    ∃ R : ℝ, v < R ∧ ENNReal.ofReal R < C := by
  by_cases htop : C = ⊤
  · refine ⟨v + 1, by linarith, ?_⟩
    simp [htop]
  · have hvC : v < C.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal hv0 htop).mp hv
    refine ⟨(v + C.toReal) / 2, ?_, ?_⟩
    · linarith
    · have hRpos : 0 ≤ (v + C.toReal) / 2 := by
        linarith
      apply (ENNReal.ofReal_lt_iff_lt_toReal hRpos htop).mpr
      linarith
