-- Prove2me | solution 1 for AvramDividend.Classical.capped_postPaymentReserve_initial_state
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:06:41.242832+00:00
-- url     : https://prove2.me/submissions/97607bae-1553-45a5-83ef-e284c7bfab5e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (ω : Ω) :
    0 ≤ x + X.X 0 ω - rightLimit D 0 ω ∧
      ENNReal.ofReal (x + X.X 0 ω - rightLimit D 0 ω) ≤ C := by
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have h0 : D 0 ω = 0 := hs.1 ω
  have hX0 : X.X 0 ω = 0 := X.X_zero ω
  have hadm :
      rightLimit D 0 ω - D 0 ω ≤ riskProcess X x D 0 ω :=
    hD.1.2 ω 0 (Or.inl rfl)
  have hnonneg : 0 ≤ x + X.X 0 ω - rightLimit D 0 ω := by
    dsimp [riskProcess] at hadm
    rw [h0, hX0] at hadm
    linarith
  have hupper :
      x + X.X 0 ω - rightLimit D 0 ω ≤ x := by
    have h :=
      (postPaymentReserve_rightJump_decomposition X x D hs ω 0).2.2
    simpa [riskProcess, h0, hX0] using h
  exact ⟨hnonneg, (ENNReal.ofReal_mono hupper).trans hxc⟩
