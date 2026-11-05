-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_full_cash_physical_hjb_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:07:25.72272+00:00
-- url     : https://prove2.me/submissions/1370c4f1-cc80-48ba-b9af-8e6c19f8f50c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical HJB bounds original paid cash atoms in ENNReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (ω : Ω) (T : ℝ≥0) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧ μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      (∀ t : ℝ≥0, t ≤ T →
        μatom {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∑' a : {t : ℝ | t ∈ A ∧
          t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0},
        ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}) ≤
      ∑' a : {t : ℝ | t ∈ A ∧
          t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0},
        ENNReal.ofReal (Real.exp (-(q * a.1))) *
          ENNReal.ofReal
            (w (riskProcess X x D (Real.toNNReal a.1) ω) -
              w (riskProcess X x D (Real.toNNReal a.1) ω -
                (rightLimit D (Real.toNNReal a.1) ω -
                  D (Real.toNNReal a.1) ω))) := by
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hNull, hAc, hDiffuse,
    hRight, hSummable, hCashEq⟩ :=
    avram_p4_f_assembly_original_full_cash_paid_nonzero_atom_decomposition
      X x D hD q hq ω T
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hNull, hAc,
    hDiffuse, hRight, ?_⟩
  let E : Set ℝ := {t | t ∈ A ∧
    t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
  have hPhysical :=
    avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
      X x D w hjump ω T A μatom μdiffuse hSplit hRight
  have hMass : ∀ a : E,
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω) := by
    intro a
    rcases hPhysical a with ⟨_, _, _, _, hAtomMass, _⟩
    exact hAtomMass
  have hPaid : ∀ a : E,
      Real.toNNReal a.1 = 0 ∨
        (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω := by
    intro a
    rcases hPhysical a with ⟨_, _, hEligibility, _, _, _⟩
    exact hEligibility
  exact avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
    X x D w q hjump ω E μatom hMass hPaid
