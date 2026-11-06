-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:52:44.080899+00:00
-- url     : https://prove2.me/submissions/44a3bc89-211a-411c-8a81-921082b12fa5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_surviving_pre_rightpayment_terminal_left_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- On strict survival of a positive deterministic horizon, the discounted
original post-rightpayment values approaching the horizon from below converge
almost surely to the pre-rightpayment terminal value at that horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun s : ℝ≥0 =>
        Real.exp (-(q * (s : ℝ))) *
          w (x + X.X s ω - rightLimit D s ω))
        (𝓝[<] t)
        (𝓝 (Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω))) := by
  filter_upwards [avram_p3_2_original_surviving_pre_rightpayment_terminal_left_tendsto_ae
    X D hD.1.1 x t ht] with ω hReserve
  intro hSurvive
  let f : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
  have hNear : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, f s ∈ Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsruin : (s : ℝ≥0∞) < ruinTime X x D ω :=
      lt_trans ((ENNReal.coe_lt_coe).2 hs) hSurvive
    have hNonneg := hD.1.2 ω s (Or.inr hsruin)
    change 0 ≤ f s
    dsimp [f, riskProcess] at *
    linarith
  have hTnonneg : riskProcess X x D t ω ∈ Ici (0 : ℝ) := by
    have hPost := hD.1.2 ω t (Or.inr hSurvive)
    have hPay := dividendStrategy_le_rightLimit D hD.1.1 ω t
    change 0 ≤ riskProcess X x D t ω
    dsimp [riskProcess] at *
    linarith
  have hWithin : Tendsto f (𝓝[<] t)
      (𝓝[Ici (0 : ℝ)] (riskProcess X x D t ω)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hReserve, hNear⟩
  have hW : Tendsto (fun s => w (f s)) (𝓝[<] t)
      (𝓝 (w (riskProcess X x D t ω))) :=
    (hw_cont.continuousWithinAt hTnonneg).tendsto.comp hWithin
  have hExpCont : Continuous (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ)))) := by
    fun_prop
  have hExp : Tendsto (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))))
      (𝓝[<] t) (𝓝 (Real.exp (-(q * (t : ℝ))))) :=
    (hExpCont.tendsto t).mono_left nhdsWithin_le_nhds
  simpa only [f] using hExp.mul hW
