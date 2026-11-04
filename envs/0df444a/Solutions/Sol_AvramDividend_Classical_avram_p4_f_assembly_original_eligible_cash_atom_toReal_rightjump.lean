-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_eligible_cash_atom_toReal_rightjump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:50:00.204211+00:00
-- url     : https://prove2.me/submissions/b77457a4-d2d1-4a93-8d9b-7642a14d7cd8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- An eligible original Cash index is the true real discounted right jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom : Measure ℝ) (q a : ℝ)
    (hAtom : ∀ t : ℝ≥0, t ≤ T →
      μatom {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω))
    (hDelta : ∀ t : ℝ≥0, t ≤ T →
      0 ≤ rightLimit D t ω - D t ω)
    (ha : a ∈ Icc (0 : ℝ) (T : ℝ))
    (hpay : a ∈ paymentTimes (ruinTime X x D ω)) :
    ((if a ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a))) else 0) *
      μatom {a}).toReal =
      Real.exp (-(q * a)) *
        (rightLimit D (⟨a, ha.1⟩ : ℝ≥0) ω -
          D (⟨a, ha.1⟩ : ℝ≥0) ω) := by
  let t : ℝ≥0 := ⟨a, ha.1⟩
  have ht : t ≤ T := by
    dsimp [t]
    exact_mod_cast ha.2
  have h := avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
    D ω q t μatom (hAtom t ht) (hDelta t ht)
  rw [if_pos hpay]
  exact h
