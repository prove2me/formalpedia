-- Prove2me | solution 1 for AvramDividend.Classical.sampledRiskProcess_hittingBtwn_le_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:21:27.777976+00:00
-- url     : https://prove2.me/submissions/fcaaf4ce-40f6-4d1a-9f5a-ad301ed86c4f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (δ : ℝ≥0) (N : ℕ) (ω : Ω) :
    ((hittingBtwn
      (fun k : ℕ => fun ω =>
        riskProcess X x D ((k : ℝ≥0) * δ) ω)
      (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ) ≤
      (N : WithTop ℕ) := by
  have h :=
    hittingBtwn_mem_Icc
      (u := fun k : ℕ => fun ω =>
        riskProcess X x D ((k : ℝ≥0) * δ) ω)
      (s := Iio (0 : ℝ)) (Nat.zero_le N) ω
  exact_mod_cast h.2
