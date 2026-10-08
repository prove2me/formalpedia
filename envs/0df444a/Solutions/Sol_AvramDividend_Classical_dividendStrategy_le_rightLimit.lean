-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_le_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:28:54.270354+00:00
-- url     : https://prove2.me/submissions/5cba712c-4c79-4ca3-8e7a-879d5233fecc

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    D t ω ≤ rightLimit D t ω := by
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.2.1 ω
  unfold rightLimit
  let s0 : Ioi t := ⟨t + 1, lt_add_of_pos_right t zero_lt_one⟩
  letI : Nonempty (Ioi t) := ⟨s0⟩
  apply le_ciInf
  intro s
  exact hmono (le_of_lt s.2)
