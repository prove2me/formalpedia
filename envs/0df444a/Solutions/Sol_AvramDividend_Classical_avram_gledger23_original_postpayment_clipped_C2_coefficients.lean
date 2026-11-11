-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger23_original_postpayment_clipped_C2_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:55:47.220202+00:00
-- url     : https://prove2.me/submissions/4aef0441-f8e1-4270-aca4-cf59af89af35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The *actual postpayment* reserve on the original X,D space gives
    right-continuous-filtration measurable, bounded Gaussian coefficients. -/
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
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      x + X.X t ω - rightLimit D t ω
    let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
    let G : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω ∧ Y s ω ∈ Icc a b then
        Real.exp (-(q * (s : ℝ))) *
          (if interior (Y s ω) then deriv w (Y s ω) else 0)
      else 0
    let H : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω ∧ Y s ω ∈ Icc a b then
        Real.exp (-(q * (s : ℝ))) *
          (if interior (Y s ω) then iteratedDeriv 2 w (Y s ω) else 0)
      else 0
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ s : ℝ≥0, Measurable[𝓕.rightCont s] (G s) ∧
        Measurable[𝓕.rightCont s] (H s) ∧
        (∀ ω, |G s ω| ≤ KG ∧ |H s ω| ≤ KH) := by
  classical
  dsimp only
  let a := min x ((1 : ℝ) / ((j : ℝ) + 1))
  let b := x + ((j : ℝ) + 1)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
    x + X.X t ω - rightLimit D t ω
  let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
  let G : ℝ≥0 → Ω → ℝ := fun s ω =>
    if s < ρ ω ∧ Y s ω ∈ Icc a b then
      Real.exp (-(q * (s : ℝ))) *
        (if interior (Y s ω) then deriv w (Y s ω) else 0)
    else 0
  let H : ℝ≥0 → Ω → ℝ := fun s ω =>
    if s < ρ ω ∧ Y s ω ∈ Icc a b then
      Real.exp (-(q * (s : ℝ))) *
        (if interior (Y s ω) then iteratedDeriv 2 w (Y s ω) else 0)
    else 0
  change ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
    ∀ s : ℝ≥0, Measurable[𝓕.rightCont s] (G s) ∧
      Measurable[𝓕.rightCont s] (H s) ∧
      (∀ ω, |G s ω| ≤ KG ∧ |H s ω| ≤ KH)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min hx (one_div_pos.mpr (by positivity))
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
  have hXmeas : Measurable[𝓕.rightCont s] (X.X s) :=
    (X.adapted s).mono (𝓕.le_rightCont s) le_rfl
  have hDmeas : Measurable[𝓕.rightCont s] (rightLimit D s) :=
    (dividendStrategy_rightLimit_adapted_rightCont D hD) s
  have hY : Measurable[𝓕.rightCont s] (Y s) := by
    dsimp [Y]
    exact (measurable_const.add hXmeas).sub hDmeas
  have hMask : MeasurableSet[𝓕.rightCont s] {ω : Ω | s < ρ ω} := by
    have hs := hρstop s
    have he : {ω : Ω | s < ρ ω} = {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ s}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, WithTop.coe_le_coe, not_le]
    rw [he]
    exact hs.compl
  have hIn : MeasurableSet[𝓕.rightCont s]
      {ω : Ω | Y s ω ∈ Icc a b} := measurableSet_Icc.preimage hY
  have hEvent : MeasurableSet[𝓕.rightCont s]
      {ω : Ω | s < ρ ω ∧ Y s ω ∈ Icc a b} := hMask.inter hIn
  have hGM : Measurable[𝓕.rightCont s] (G s) :=
    Measurable.ite hEvent (measurable_const.mul (hGrad.comp hY)) measurable_const
  have hHM : Measurable[𝓕.rightCont s] (H s) :=
    Measurable.ite hEvent (measurable_const.mul (hHess.comp hY)) measurable_const
  refine ⟨hGM, hHM, ?_⟩
  intro ω
  by_cases he : s < ρ ω ∧ Y s ω ∈ Icc a b
  · have hi : interior (Y s ω) := hBand he.2
    have hG1 := hGB s (Y s ω) he.2
    have hH1 := hHB s (Y s ω) he.2
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
