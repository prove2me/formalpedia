-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_eligible_paid_atoms_physical_hjb_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:01:42.277911+00:00
-- url     : https://prove2.me/submissions/9cfb1eb4-6def-4fab-b9a5-71f255a84946

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An original paid atom needs no separately supplied mass or eligibility hypotheses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (ω : Ω) (T : ℝ≥0) (A : Set ℝ)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hRight : ∀ u : ℝ≥0, u ≤ T →
      μatom {(u : ℝ)} =
        ENNReal.ofReal (rightLimit D u ω - D u ω)) :
    let E : Set ℝ := {t | t ∈ A ∧
      t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
    (∑' a : E,
      ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}) ≤
    ∑' a : E,
      ENNReal.ofReal (Real.exp (-(q * a.1))) *
        ENNReal.ofReal
          (w (riskProcess X x D (Real.toNNReal a.1) ω) -
            w (riskProcess X x D (Real.toNNReal a.1) ω -
              (rightLimit D (Real.toNNReal a.1) ω -
                D (Real.toNNReal a.1) ω))) := by
  dsimp only
  let E : Set ℝ := {t | t ∈ A ∧
    t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
  have hPhysical :=
    avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
      X x D w hjump ω T A μatom μdiffuse hsplit hRight
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
