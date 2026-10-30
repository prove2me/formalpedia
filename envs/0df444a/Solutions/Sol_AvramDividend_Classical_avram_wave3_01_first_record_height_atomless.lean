-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_first_record_height_atomless
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T01:16:33.94867+00:00
-- url     : https://prove2.me/submissions/a8e15de3-7daa-4d9f-803d-8318bc6b233f

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_purejump_allFiniteHorizon_height_atomless

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Before a finite first upward record, a pure infinite-variation Lévy
    reflected drawdown has no atom at a specified positive running height. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a c : ℝ≥0, a < c →
      ∃ m : ℕ, a < times m ∧ times m < c)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    P {ω : Ω | ∃ u : ℝ≥0,
      (u : ℝ≥0∞) = twoSidedExitUpTime X b ω ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) = (x : ℝ)} = 0 := by
  have hSubset :
      {ω : Ω | ∃ u : ℝ≥0,
        (u : ℝ≥0∞) = twoSidedExitUpTime X b ω ∧
        sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) = (x : ℝ)} ⊆
      {ω : Ω | ∃ H : ℝ≥0,
        sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
        reflectedSup X H ω < (x : ℝ)} := by
    intro ω hω
    rcases hω with ⟨u, hu, hheight⟩
    refine ⟨u, hheight, ?_⟩
    have hRecord : runningSup X u ω - X.X u ω = 0 :=
      firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
    change runningSup X u ω - X.X u ω < (x : ℝ)
    rw [hRecord]
    exact_mod_cast hx
  apply le_antisymm ?_ (by exact zero_le)
  calc
    P {ω : Ω | ∃ u : ℝ≥0,
      (u : ℝ≥0∞) = twoSidedExitUpTime X b ω ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) = (x : ℝ)}
      ≤ P {ω : Ω | ∃ H : ℝ≥0,
        sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
        reflectedSup X H ω < (x : ℝ)} := measure_mono hSubset
    _ = 0 := avram_wave3_01_purejump_allFiniteHorizon_height_atomless
      X x hx times horizons hdense hpos hcofinal hjump
