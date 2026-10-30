-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_uniform_bounded_height_atomless
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:52:56.988988+00:00
-- url     : https://prove2.me/submissions/d1611a88-7f6c-4c2f-bb7f-83d0e1c9c2e1

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_terminal_below_max_capped_first_hit_geometry
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_reflectedSup_exceeds_hit_height_of_negative_posthit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A single null event controls all bounded terminal horizons, including random ones. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (N : ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    P {ω : Ω | ∃ H : ℝ≥0, H ≤ N ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 H) = (x : ℝ) ∧
      reflectedSup X H ω < (x : ℝ)} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [
    reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
      X N (x : ℝ) times horizons hdense hpos hcofinal hRegular
  ] with ω hω
  rintro ⟨H, hHN, hMax, hEnd⟩
  let R : ℝ≥0 → ℝ := fun t => reflectedSup X t ω
  let hit (B : ℝ≥0) : Set ℝ≥0 := Icc (0 : ℝ≥0) B ∩ R ⁻¹' Ici (x : ℝ)
  let T (B : ℝ≥0) : ℝ≥0 := sInf (hit B ∪ {B})
  obtain ⟨hTH, hTx, hBound⟩ :=
    reflectedSup_terminal_below_max_capped_first_hit_geometry
      X ω H (x : ℝ) (by exact_mod_cast hx) hMax hEnd
  have hTmem : T H ∈ hit N ∪ {N} := by
    left
    exact ⟨⟨zero_le, (le_of_lt hTH).trans hHN⟩, by
      change (x : ℝ) ≤ R (T H)
      simpa [T, hit, R] using hTx.ge⟩
  have hTNle : T N ≤ T H := by
    exact csInf_le (by exact ⟨0, by intro a ha; exact zero_le⟩) hTmem
  have hTHle : T H ≤ T N := by
    apply le_csInf
    · exact ⟨N, by simp [T, hit]⟩
    · intro u hu
      rcases hu with hHit | hCap
      · rcases hHit with ⟨⟨_, huN⟩, huR⟩
        by_cases huH : u ≤ H
        · exact csInf_le (by exact ⟨0, by intro a ha; exact zero_le⟩)
            (Or.inl ⟨⟨zero_le, huH⟩, huR⟩)
        · exact le_trans (le_of_lt hTH) (le_of_lt (lt_of_not_ge huH))
      · rcases hCap with rfl
        exact (le_of_lt hTH).trans hHN
  have hT_eq : T N = T H := le_antisymm hTNle hTHle
  have hDown : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (T H + s) ω - X.X (T H) ω < 0 := by
    simpa only [T, hit, R, hT_eq] using hω
  have hTH' : T H < H := by
    simpa only [T, hit, R] using hTH
  have hTx' : reflectedSup X (T H) ω = (x : ℝ) := by
    simpa only [T, hit, R] using hTx
  obtain ⟨t, -, htH, hlt⟩ :=
    reflectedSup_exceeds_hit_height_of_negative_posthit X ω (T H) H x
      hTH' hTx'
      (fun ε hε => by
        obtain ⟨s, hs, hneg⟩ := hDown ε hε
        refine ⟨s, hs, ?_⟩
        change X.X (T H + s) ω < X.X (T H) ω
        calc
          X.X (T H + s) ω =
              X.X (T H) ω + (X.X (T H + s) ω - X.X (T H) ω) := by ring
          _ < X.X (T H) ω + 0 := add_lt_add_right hneg _
          _ = X.X (T H) ω := by ring)
  linarith [hBound t htH.le]
