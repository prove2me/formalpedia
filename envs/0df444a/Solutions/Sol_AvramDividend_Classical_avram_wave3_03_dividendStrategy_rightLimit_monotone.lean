-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_dividendStrategy_rightLimit_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:27:00.734353+00:00
-- url     : https://prove2.me/submissions/2027f2bc-eb7d-433f-b76a-c55911fc48d0

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual strict-right dividend limit remains monotone, including at
    the time-zero dividend atom and every subsequent jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) : Monotone (fun t : ℝ≥0 => rightLimit D t ω) := by
  intro s t hst
  have hmono : Monotone (fun u : ℝ≥0 => D u ω) := hD.2.1 ω
  unfold rightLimit
  letI : Nonempty (Ioi s) :=
    ⟨⟨s + 1, lt_add_of_pos_right s zero_lt_one⟩⟩
  letI : Nonempty (Ioi t) :=
    ⟨⟨t + 1, lt_add_of_pos_right t zero_lt_one⟩⟩
  have hb : BddBelow (Set.range (fun u : Ioi s => D u ω)) := by
    refine ⟨D s ω, ?_⟩
    rintro y ⟨u, rfl⟩
    exact hmono (le_of_lt u.2)
  apply le_ciInf
  intro u
  have hsu : s < (u : ℝ≥0) := lt_of_le_of_lt hst u.2
  exact ciInf_le hb (⟨u, hsu⟩ : Ioi s)
