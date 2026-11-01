-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_full_right_payment_jump_support_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:12:38.677994+00:00
-- url     : https://prove2.me/submissions/fbc4e6f3-8d07-4ce9-899e-5029dffb58d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_right_atom_masses_real_summable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_atom_support_eq_right_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_actual_right_payment_jumps_summable_on_atom_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Every actual chronological right-payment jump on a finite window is
in the countable atomic carrier of the full Stieltjes dividend measure.
Restricting the finite real atom-mass sum then controls the complete
set of positive jumps, without excluding singular-continuous dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let A : Set ℝ :=
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
        0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
    A.Countable ∧
      Summable (fun s : A =>
        rightLimit D ((s : ℝ).toNNReal) ω -
        D ((s : ℝ).toNNReal) ω) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  let A : Set ℝ :=
    {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
  obtain ⟨B, μatom, μdiffuse, hBcount, hBmeas, hdecomp,
    hAtomSum, hAtomSupport, hNull, hMass, hBound⟩ :=
    avram_wave4_04b_finite_horizon_right_atom_masses_real_summable
      D hD ω T
  have hEqSupport : {s : ℝ | μ {s} ≠ 0} = A := by
    exact avram_wave4_04b_finite_horizon_atom_support_eq_right_jumps
      D hD ω T
  have hAinB : A ⊆ B := by
    intro s hsA
    have hμpos : μ {s} ≠ 0 := by
      have : s ∈ {s : ℝ | μ {s} ≠ 0} := by
        rw [hEqSupport]
        exact hsA
      exact this
    by_contra hsB
    have hSingSubset : ({s} : Set ℝ) ⊆ Bᶜ := by
      intro x hx
      have hxs : x = s := hx
      subst x
      exact hsB
    have hAtomZero : μatom {s} = 0 := by
      apply le_antisymm ?_ bot_le
      calc
        μatom {s} ≤ μatom Bᶜ := measure_mono hSingSubset
        _ = 0 := hAtomSupport
    have hDiffuseZero : μdiffuse {s} = 0 := by
      letI : NullSingletonClass μdiffuse := hNull
      simp
    have hμzero : μ {s} = 0 := by
      calc
        μ {s} = (μatom + μdiffuse) {s} :=
          congrArg (fun ν : Measure ℝ => ν {s}) hdecomp
        _ = 0 := by simp [hAtomZero, hDiffuseZero]
    exact hμpos hμzero
  have hAcount : A.Countable := hBcount.mono hAinB
  let f : A → B := fun s => ⟨s.1, hAinB s.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : B => (z : ℝ)) hxy
  have hMassA :
      Summable (fun s : A => (μ {(s : ℝ)}).toReal) := by
    have hComp := hMass.comp_injective hf
    change Summable (fun s : A => (μ {(f s : ℝ)}).toReal) at hComp
    simpa only [f] using hComp
  have hWindow (s : A) :
      (0 : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (T : ℝ) := by
    exact ⟨s.property.1, s.property.2.1⟩
  have hDsum :
      Summable (fun s : A =>
        rightLimit D ((s : ℝ).toNNReal) ω -
        D ((s : ℝ).toNNReal) ω) :=
    avram_wave4_04b_finite_horizon_actual_right_payment_jumps_summable_on_atom_support
      D hD ω T A hWindow hMassA
  exact ⟨hAcount, hDsum⟩
