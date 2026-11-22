-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_randomclock_physical_mark_quantizer_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:24:04.238409+00:00
-- url     : https://prove2.me/submissions/8adb953c-2c2f-448c-ada4-4e48df076d96

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_simple_mark_integrals_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

/-- The actual physical bounded-mark quantizers converge on every bounded random clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
    (g : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hfBound : ∀ k z, z ∈
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1))) →
      |f k z| ≤ 1)
    (hfLimit : ∀ z ∈
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1))),
      Tendsto (fun k => f k z) atTop (𝓝 (g z)))
    (ρ : Ω → ℝ≥0) (hρ : ∀ ω, ρ ω ≤ T) :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let F : ℕ → Ω → ℝ := fun k ω =>
      ∫ p in Ioc 0 (ρ ω) ×ˢ B, f k p.2 ∂NX ω
    let J : Ω → ℝ := fun ω =>
      ∫ p in Ioc 0 (ρ ω) ×ˢ B, g p.2 ∂NX ω
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    (∀ ω k, |F k ω| ≤ N ω) ∧
    (∀ ω, Tendsto (fun k => F k ω) atTop (𝓝 (J ω))) := by
  classical
  intro B NX F J N
  have hBm : MeasurableSet B := measurableSet_Ioc
  have hMass (ω : Ω) : NX ω (Ioc 0 T ×ˢ B) < ⊤ := by
    have hSub : Ioc 0 T ×ˢ B ⊆
        Ioc 0 T ×ˢ Iic (-(1 / ((b : ℝ) + 1))) :=
      Set.prod_mono Subset.rfl (fun z hz => hz.2)
    have hh :=
      avram_wave7_06_original_separated_negative_band_count_finite_every_path
        X ω T b
    exact lt_of_le_of_lt (measure_mono hSub) (by simpa [NX] using hh)
  have hSubρ (ω : Ω) :
      Ioc 0 (ρ ω) ×ˢ B ⊆ Ioc 0 T ×ˢ B := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (hρ ω)⟩, hp.2⟩
  have hMassρ (ω : Ω) :
      NX ω (Ioc 0 (ρ ω) ×ˢ B) < ⊤ :=
    lt_of_le_of_lt (measure_mono (hSubρ ω)) (hMass ω)
  constructor
  · intro ω k
    have hh :=
      (avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
        (NX ω) (ρ ω) B hBm (fun z => f k z)
        (f k).measurable (hMassρ ω)
        (fun z hz => hfBound k z hz)).2
    have hCount :
        (NX ω (Ioc 0 (ρ ω) ×ˢ B)).toReal ≤
          (NX ω (Ioc 0 T ×ˢ B)).toReal :=
      ENNReal.toReal_mono (ne_of_lt (hMass ω)) (measure_mono (hSubρ ω))
    have hFirst : |F k ω| ≤
        (NX ω (Ioc 0 (ρ ω) ×ˢ B)).toReal := by
      simpa only [F] using hh
    exact hFirst.trans hCount
  · intro ω
    exact avram_a20_original_bounded_simple_mark_integrals_tendsto
      (NX ω) (ρ ω) B hBm (hMassρ ω) g f hfBound hfLimit
