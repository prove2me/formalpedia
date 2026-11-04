-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_generator_dividend_mesh_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:52:49.243033+00:00
-- url     : https://prove2.me/submissions/6ce90ca0-7c5f-4bc7-b104-4ea26af3ae58

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_discounted_postpayment_generator_mesh_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_discounted_right_dividend_atom_mesh_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Combine the original Lévy generator and right-dividend mesh residuals.
    This is a sign ledger; the source Itô martingale cell estimate remains open. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (N : ℕ) (clock : Fin N → ℝ≥0) (δ : Fin N → ℝ) (ω : Ω)
    (hδ : ∀ i, 0 ≤ δ i)
    (hpos : ∀ i, 0 < x + X.X (clock i) ω - rightLimit D (clock i) ω)
    (hcap : ∀ i, ENNReal.ofReal (x + X.X (clock i) ω -
      rightLimit D (clock i) ω) < C)
    (hclock : ∀ i, clock i = 0 ∨
      (clock i : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i : Fin N,
      (δ i * Real.exp (-(q * (clock i : ℝ)))) *
        (X.generator w (x + X.X (clock i) ω - rightLimit D (clock i) ω) -
         q * w (x + X.X (clock i) ω - rightLimit D (clock i) ω))) +
    (∑ i : Fin N,
      Real.exp (-(q * (clock i : ℝ))) *
        ((rightLimit D (clock i) ω - D (clock i) ω) -
         (w (riskProcess X x D (clock i) ω) -
          w (riskProcess X x D (clock i) ω -
            (rightLimit D (clock i) ω - D (clock i) ω))))) ≤ 0 := by
  have hg :=
    avram_wave7_08_source_discounted_postpayment_generator_mesh_nonpositive
      X q w C hw_gen x D N clock δ ω hδ hpos hcap
  have hd :=
    avram_wave7_08_source_discounted_right_dividend_atom_mesh_nonpositive
      X q x w D hjump N clock ω hclock
  linarith
