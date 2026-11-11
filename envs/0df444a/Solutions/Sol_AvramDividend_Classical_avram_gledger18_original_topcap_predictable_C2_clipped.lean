-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger18_original_topcap_predictable_C2_clipped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:51:35.957165+00:00
-- url     : https://prove2.me/submissions/f641c9d3-6bae-4163-b74a-ef4bf4aa73d3

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped reserve gives predictable, globally bounded C²
coefficients after clipping to a positive compact surplus band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (j : ℕ) :
    let a := min x ((1 : ℝ) / ((j : ℝ) + 1))
    let b := x + ((j : ℝ) + 1)
    let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
    let G : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω ∧ riskProcess X x D s ω ∈ Icc a b then
        Real.exp (-(q * (s : ℝ))) *
          (if interior (riskProcess X x D s ω) then
            deriv w (riskProcess X x D s ω) else 0)
      else 0
    let H : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω ∧ riskProcess X x D s ω ∈ Icc a b then
        Real.exp (-(q * (s : ℝ))) *
          (if interior (riskProcess X x D s ω) then
            iteratedDeriv 2 w (riskProcess X x D s ω) else 0)
      else 0
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ s : ℝ≥0, Measurable[𝓕.rightCont s] (G s) ∧
        Measurable[𝓕.rightCont s] (H s) ∧
        (∀ ω, |G s ω| ≤ KG ∧ |H s ω| ≤ KH) := by
  classical
  dsimp only
  let a := min x ((1 : ℝ) / ((j : ℝ) + 1))
  let b := x + ((j : ℝ) + 1)
  let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
  let G : ℝ≥0 → Ω → ℝ := fun s ω =>
    if s < ρ ω ∧ riskProcess X x D s ω ∈ Icc a b then
      Real.exp (-(q * (s : ℝ))) *
        (if interior (riskProcess X x D s ω) then deriv w (riskProcess X x D s ω) else 0)
    else 0
  let H : ℝ≥0 → Ω → ℝ := fun s ω =>
    if s < ρ ω ∧ riskProcess X x D s ω ∈ Icc a b then
      Real.exp (-(q * (s : ℝ))) *
        (if interior (riskProcess X x D s ω) then iteratedDeriv 2 w (riskProcess X x D s ω) else 0)
    else 0
  change ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
    ∀ s : ℝ≥0, Measurable[𝓕.rightCont s] (G s) ∧
      Measurable[𝓕.rightCont s] (H s) ∧
      (∀ ω, |G s ω| ≤ KG ∧ |H s ω| ≤ KH)
  have ha : 0 < a := by
    dsimp [a]
    apply lt_min hx
    exact one_div_pos.mpr (by positivity)
  have hOpen : IsOpen {y : ℝ | interior y} := by
    change IsOpen (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' Iio C)
    exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hBand : Icc a b ⊆ {y : ℝ | interior y} := by
    intro y hy
    change interior y
    refine ⟨lt_of_lt_of_le ha hy.1, ?_⟩
    simp [hTopCap]
  obtain ⟨KG, KH, hKG, hKH, hGB, hHB⟩ :=
    avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
      X hBV hν q hq C w hw hOpen a b hBand
  have hGrad : Measurable (fun y : ℝ => if interior y then deriv w y else 0) :=
    avram_wave4_04b_measurable_cap_interior_deriv_zero_extension w C hw
  have hHess : Measurable (fun y : ℝ => if interior y then iteratedDeriv 2 w y else 0) :=
    avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension w C hw
  refine ⟨KG, KH, hKG, hKH, ?_⟩
  intro s
  have hY : Measurable[𝓕.rightCont s] (riskProcess X x D s) :=
    ((riskProcess_adapted X x D hD) s).mono (𝓕.le_rightCont s) le_rfl
  have hMask : MeasurableSet[𝓕.rightCont s] {ω : Ω | s < ρ ω} := by
    have hs := hρstop s
    have he : {ω : Ω | s < ρ ω} = {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ s}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, WithTop.coe_le_coe, not_le]
    rw [he]
    exact hs.compl
  have hIn : MeasurableSet[𝓕.rightCont s]
      {ω : Ω | riskProcess X x D s ω ∈ Icc a b} :=
    measurableSet_Icc.preimage hY
  have hEvent : MeasurableSet[𝓕.rightCont s]
      {ω : Ω | s < ρ ω ∧ riskProcess X x D s ω ∈ Icc a b} :=
    hMask.inter hIn
  have hGM : Measurable[𝓕.rightCont s] (G s) :=
    Measurable.ite hEvent
      (measurable_const.mul (hGrad.comp hY)) measurable_const
  have hHM : Measurable[𝓕.rightCont s] (H s) :=
    Measurable.ite hEvent
      (measurable_const.mul (hHess.comp hY)) measurable_const
  refine ⟨hGM, hHM, ?_⟩
  intro ω
  by_cases he : s < ρ ω ∧ riskProcess X x D s ω ∈ Icc a b
  · have hi : interior (riskProcess X x D s ω) := hBand he.2
    have hG1 := hGB s (riskProcess X x D s ω) he.2
    have hH1 := hHB s (riskProcess X x D s ω) he.2
    constructor
    · change |G s ω| ≤ KG
      simp only [G, if_pos he, if_pos hi]
      exact hG1
    · change |H s ω| ≤ KH
      simp only [H, if_pos he, if_pos hi]
      exact hH1
  · constructor
    · change |G s ω| ≤ KG
      simp only [G, if_neg he, abs_zero]
      exact hKG
    · change |H s ω| ≤ KH
      simp only [H, if_neg he, abs_zero]
      exact hKH
