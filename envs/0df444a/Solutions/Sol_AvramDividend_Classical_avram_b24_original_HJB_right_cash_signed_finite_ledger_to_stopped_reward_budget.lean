-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_HJB_right_cash_signed_finite_ledger_to_stopped_reward_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:21:02.879163+00:00
-- url     : https://prove2.me/submissions/5ed49ac4-6642-44d8-8e5a-a10a4d24c818

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
import Theorems.Thm_AvramDividend_Classical_avram_b24_signed_mesh_cash_telescope_of_aggregate_HJB_right_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (N : ℕ) (s t : ℕ → ℝ≥0) (y : ℕ → ℝ)
    (active : ℕ → Bool) (ω : Ω) (R : Finset ℝ≥0)
    (hTimes : ∀ i ∈ Finset.range N, s i ≤ t i)
    (hInterior : ∀ i ∈ Finset.range N, active i = true →
      0 < y i ∧ ENNReal.ofReal (y i) < C)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (V cash gaussian jump drift error : ℕ → ℝ) (cash0 : ℝ)
    (hInitial : V 0 + cash0 ≤ w x)
    (hCell : ∀ i : ℕ, i < N →
      V (i + 1) + cash i ≤
        V i + gaussian i + jump i + drift i + error i)
    (hDrift : (∑ i ∈ Finset.range N, drift i) =
      (∑ i ∈ Finset.range N, if active i then
        Real.exp (-(q * (s i : ℝ))) *
          ((t i : ℝ) - (s i : ℝ)) *
          (X.generator w (y i) - q * w (y i))
        else 0) +
      (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
        ((rightLimit D u ω - D u ω) -
          (w (riskProcess X x D u ω) -
            w (riskProcess X x D u ω -
              (rightLimit D u ω - D u ω)))))) :
    V N + cash0 + (∑ i ∈ Finset.range N, cash i) ≤
      w x + (∑ i ∈ Finset.range N, gaussian i) +
        (∑ i ∈ Finset.range N, jump i) +
        (∑ i ∈ Finset.range N, error i) := by
  have hSign :=
    avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
      X q hq w C hC hgen x D hjump
      (Finset.range N) s t y active hTimes hInterior ω R hPre
  have hDriftNonpos : (∑ i ∈ Finset.range N, drift i) ≤ 0 := by
    rw [hDrift]
    exact hSign
  exact avram_b24_signed_mesh_cash_telescope_of_aggregate_HJB_right_sign
    N (w x) cash0 V cash gaussian jump drift error
    hInitial hCell hDriftNonpos
