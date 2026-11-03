-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_original_finite_ito_ledger_with_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:48:54.799261+00:00
-- url     : https://prove2.me/submissions/2f31ada4-949f-4c48-9c84-221e22f3960a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_finite_mesh_ito_ledger
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

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
    (N : ℕ) :
    Real.exp (-(q * (clock N : ℝ))) *
        w (x + X.X (clock N) ω - rightLimit D (clock N) ω) +
      rightLimit D 0 ω + (∑ k ∈ Finset.range N, CashInc k) ≤
      w x + (∑ k ∈ Finset.range N, MInc k) +
        (∑ k ∈ Finset.range N, GInc k) +
        (∑ k ∈ Finset.range N, HInc k) := by
  have hinit : V 0 + rightLimit D 0 ω ≤ w x := by
    calc
      V 0 + rightLimit D 0 ω =
          w (x - rightLimit D 0 ω) + rightLimit D 0 ω := by
            rw [hV 0, hclock0]
            simp [X.X_zero ω]
      _ ≤ w x :=
        avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
          X w x C D hD hjump ω
  exact avram_wave7_08_source_original_finite_mesh_ito_ledger
    X q x w D clock ω V hV
    (rightLimit D 0 ω) CashInc MInc GInc HInc hinit hcell N
