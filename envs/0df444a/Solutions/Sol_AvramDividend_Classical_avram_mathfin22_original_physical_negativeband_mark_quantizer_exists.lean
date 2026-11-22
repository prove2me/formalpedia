-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_physical_negativeband_mark_quantizer_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:19:27.675229+00:00
-- url     : https://prove2.me/submissions/96ec7fbf-9b8a-424f-84d7-eb5b1fbfe42f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_original_Borel_mark_simple_quantization
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_finiteband_simple_mark_L2dom_ae_convergence
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b) :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let J : Ω → ℝ := fun ω =>
      ∫ p in Ioc 0 T ×ˢ B, p.2 ∂NX ω
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    ∃ f : ℕ → SimpleFunc ℝ ℝ,
      (∀ k z, ‖f k z‖ ≤ 1) ∧
      (∀ z ∈ B, Tendsto (fun k => f k z) atTop (𝓝 z)) ∧
      Integrable N P ∧ Integrable (fun ω => (N ω)^2) P ∧
      (∀ᵐ ω ∂P, ∀ k,
        |∫ p in Ioc 0 T ×ˢ B, f k p.2 ∂NX ω| ≤ N ω) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun k => ∫ p in Ioc 0 T ×ˢ B, f k p.2 ∂NX ω)
          atTop (𝓝 (J ω)))  := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
  have hB : MeasurableSet B := measurableSet_Ioc
  have hLo : (-1 : ℝ) ≤ -(1 / ((a : ℝ) + 1)) := by
    have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have hd : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hh : 1 / ((a : ℝ) + 1) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ hd).2
      nlinarith
    linarith
  have hHi : -(1 / ((b : ℝ) + 1)) ≤ (0 : ℝ) := by
    have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
    have hbd : 0 ≤ (b : ℝ) + 1 := by linarith
    exact neg_nonpos.mpr (div_nonneg (by norm_num) hbd)
  have hidBound : ∀ z ∈ B, ‖z‖ ≤ 1 := by
    intro z hz
    have hzn : z ≤ 0 := le_trans hz.2 hHi
    have hzl : -1 ≤ z := le_trans hLo (le_of_lt hz.1)
    rw [Real.norm_eq_abs, abs_of_nonpos hzn]
    linarith
  obtain ⟨f, hfGlob, hfPoint⟩ :=
    avram_a20_bounded_original_Borel_mark_simple_quantization
      (fun z : ℝ => z) B measurable_id hB hidBound
  have hfBound : ∀ k z, z ∈ B → |f k z| ≤ 1 := by
    intro k z hz
    simpa [Real.norm_eq_abs] using hfGlob k z
  have hSource :=
    avram_mathfin22_original_finiteband_simple_mark_L2dom_ae_convergence
      X T a b hab (fun z => z) f hfBound hfPoint
  refine ⟨f, hfGlob, hfPoint, ?_⟩
  simpa [B] using hSource
