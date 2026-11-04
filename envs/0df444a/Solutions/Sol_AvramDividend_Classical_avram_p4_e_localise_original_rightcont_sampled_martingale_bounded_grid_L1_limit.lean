-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_rightcont_sampled_martingale_bounded_grid_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:58:05.644219+00:00
-- url     : https://prove2.me/submissions/daec6748-feed-480b-afe0-9c46cf13419a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_domination_preserves_martingale_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original right-continuous-filtration true martingale grid stops retain zero mean in a dominated limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (f : ℝ≥0 → Ω → ℝ) (hf : Martingale f 𝓕.rightCont P)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (σ : Ω → WithTop ℕ) (τk : ℕ → Ω → WithTop ℕ)
    (hσ : IsStoppingTime 𝓖 σ)
    (hτ : ∀ k, IsStoppingTime 𝓖 (τk k))
    (hle : ∀ k, σ ≤ τk k)
    (N : ℕ) (hbdd : ∀ k ω, τk k ω ≤ (N : WithTop ℕ))
    (M B : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable
      (fun ω => stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hBInt : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P,
      ‖stoppedValue (fun i : ℕ => f (e i)) (τk k) ω‖ ≤ B ω)
    (hLimitBound : ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖B ω‖)
    (hAs : ∀ᵐ ω ∂P,
      Tendsto (fun k => stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)
        atTop (𝓝 (M ω)))
    (hBase : (∫ ω, stoppedValue (fun i : ℕ => f (e i)) σ ω ∂P) = 0) :
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  let Mk : ℕ → Ω → ℝ :=
    fun k ω => stoppedValue (fun i : ℕ => f (e i)) (τk k) ω
  have hCentre : ∀ k, (∫ ω, Mk k ω ∂P) = 0 := by
    intro k
    calc
      (∫ ω, Mk k ω ∂P) =
          (∫ ω, stoppedValue (fun i : ℕ => f (e i)) σ ω ∂P) := by
        symm
        exact chat01_monotone_sampling_bounded_optional_stopping_eq
          e he hf 𝓖 h𝓖 σ (τk k) hσ (hτ k) (hle k) N (hbdd k)
      _ = 0 := hBase
  exact avram_p4_e_localise_original_domination_preserves_martingale_mean
    X Mk M B hMkMeas hMMeas hBInt hDom hLimitBound hAs hCentre