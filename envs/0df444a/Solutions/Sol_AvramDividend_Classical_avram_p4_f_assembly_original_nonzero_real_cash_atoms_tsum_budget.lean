-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_nonzero_real_cash_atoms_tsum_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:21:33.146791+00:00
-- url     : https://prove2.me/submissions/ff745162-2983-47f4-ae4c-321f837abe06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_real_indexed_cash_atom_tsum_le_value_loss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Nonzero original Stieltjes Cash atoms inherit their clock and countable HJB bound. -/
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
    (ω : Ω) (T : ℝ≥0) (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hRight : ∀ t : ℝ≥0, t ≤ T →
      μatom {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω))
    (A : Set ℝ) (hEff : ∀ a : A, μatom {a.1} ≠ 0)
    (hdelta : ∀ a : A,
      0 ≤ rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω)
    (helig : ∀ a : A, Real.toNNReal a.1 = 0 ∨
      (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω)
    (hCashSum : Summable (fun a : A =>
      (ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}).toReal))
    (hValueSum : Summable (fun a : A =>
      Real.exp (-(q * a.1)) *
        (w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω))))) :
    (∑' a : A, (ENNReal.ofReal (Real.exp (-(q * a.1))) *
      μatom {a.1}).toReal) ≤
      ∑' a : A, Real.exp (-(q * a.1)) *
        (w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω))) := by
  have hA0 : ∀ a : A, 0 ≤ a.1 := by
    intro a
    exact (avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
      D ω T μatom μdiffuse hsplit A a (hEff a)).1
  have hμatom : ∀ a : A,
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω) := by
    intro a
    have hloc := avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
      D ω T μatom μdiffuse hsplit A a (hEff a)
    have hcast : (Real.toNNReal a.1 : ℝ) = a.1 := by
      simpa [hloc.1] using (Real.coe_toNNReal a.1)
    have hclock : Real.toNNReal a.1 ≤ T := by
      exact_mod_cast (show (Real.toNNReal a.1 : ℝ) ≤ (T : ℝ) by
        simpa [hcast] using hloc.2)
    simpa [hcast] using hRight (Real.toNNReal a.1) hclock
  exact avram_p4_f_assembly_original_real_indexed_cash_atom_tsum_le_value_loss
    X x D w q hjump ω A μatom hA0 hμatom hdelta helig hCashSum hValueSum
