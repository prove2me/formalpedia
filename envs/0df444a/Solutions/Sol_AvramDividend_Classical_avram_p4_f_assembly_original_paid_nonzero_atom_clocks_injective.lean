-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_atom_clocks_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:39:15.716701+00:00
-- url     : https://prove2.me/submissions/f9db0d5e-4b68-4443-b84d-794b5612cda8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine paid nonzero source atom clocks are injective and in the stopped horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (A : Set ℝ) (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse) :
    let E : Set ℝ := {t | t ∈ A ∧
      t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
    (∀ a : E, Real.toNNReal a.1 ≤ T) ∧
    (∀ a : E, (Real.toNNReal a.1 : ℝ) ∈
      paymentTimes (ruinTime X x D ω)) ∧
    Function.Injective (fun a : E => (Real.toNNReal a.1 : ℝ)) := by
  dsimp
  let E : Set ℝ := {t | t ∈ A ∧
    t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
  have hsupport : ∀ a : E, 0 ≤ a.1 ∧ a.1 ≤ (T : ℝ) := by
    intro a
    exact avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
      D ω T μatom μdiffuse hsplit A ⟨a.1, a.2.1⟩ a.2.2.2
  have hcast : ∀ a : E, (Real.toNNReal a.1 : ℝ) = a.1 := by
    intro a
    simpa [(hsupport a).1] using (Real.coe_toNNReal a.1)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact_mod_cast (show (Real.toNNReal a.1 : ℝ) ≤ (T : ℝ) by
      simpa [hcast a] using (hsupport a).2)
  · intro a
    change (Real.toNNReal a.1 : ℝ) ∈
      paymentTimes (ruinTime X x D ω)
    rw [hcast a]
    exact a.2.2.1
  · intro a b hab
    apply Subtype.ext
    calc
      a.1 = (Real.toNNReal a.1 : ℝ) := (hcast a).symm
      _ = (Real.toNNReal b.1 : ℝ) := hab
      _ = b.1 := hcast b
