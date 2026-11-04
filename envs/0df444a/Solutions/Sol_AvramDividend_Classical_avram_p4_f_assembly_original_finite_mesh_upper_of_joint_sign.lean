-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_mesh_upper_of_joint_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:57:07.563085+00:00
-- url     : https://prove2.me/submissions/66d6a1b0-480d-48dc-8f52-0da852262707

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_finite_ito_ledger_with_zero_atom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original clock mesh, exact initial dividend, and jointly signed residuals
    yield the martingale-only stopped cash upper inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (clock : ℕ → ℝ≥0) (hclock0 : clock 0 = 0) (ω : Ω)
    (V : ℕ → ℝ)
    (hV : ∀ k, V k =
      Real.exp (-(q * (clock k : ℝ))) *
        w (x + X.X (clock k) ω - rightLimit D (clock k) ω))
    (CashInc MInc GInc HInc : ℕ → ℝ)
    (hcell : ∀ k, V (k + 1) + CashInc k ≤
      V k + MInc k + GInc k + HInc k)
    (N : ℕ)
    (hsign : (∑ k ∈ Finset.range N, GInc k) +
      (∑ k ∈ Finset.range N, HInc k) ≤ 0) :
    Real.exp (-(q * (clock N : ℝ))) *
        w (x + X.X (clock N) ω - rightLimit D (clock N) ω) +
      rightLimit D 0 ω + (∑ k ∈ Finset.range N, CashInc k) ≤
      w x + (∑ k ∈ Finset.range N, MInc k) := by
  have hledger :=
    avram_wave7_08_source_original_finite_ito_ledger_with_zero_atom
      X q w x C D hD hjump clock hclock0 ω V hV
      CashInc MInc GInc HInc hcell N
  linarith
