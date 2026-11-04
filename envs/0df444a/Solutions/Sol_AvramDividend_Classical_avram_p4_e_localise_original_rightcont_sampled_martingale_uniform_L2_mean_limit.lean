-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_rightcont_sampled_martingale_uniform_L2_mean_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:58:23.709988+00:00
-- url     : https://prove2.me/submissions/a91b6f99-3f27-4dc8-ae9a-0f579e30d34b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original right-continuous-filtration bounded grid stops yield centred limits under uniform quadratic energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
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
    (hσ : IsStoppingTime 𝓖 σ) (hτ : ∀ k, IsStoppingTime 𝓖 (τk k))
    (hle : ∀ k, σ ≤ τk k)
    (N : ℕ) (hbdd : ∀ k ω, τk k ω ≤ (N : WithTop ℕ))
    (M : Ω → ℝ)
    (hPosI : ∀ k, Integrable
      (fun ω => max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0) P)
    (hNegI : ∀ k, Integrable
      (fun ω => max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0) P)
    (hPosMeas : ∀ k, AEStronglyMeasurable
      (fun ω => max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0) P)
    (hNegMeas : ∀ k, AEStronglyMeasurable
      (fun ω => max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0) P)
    (hPosMMeas : AEStronglyMeasurable (fun ω => max (M ω) 0) P)
    (hNegMMeas : AEStronglyMeasurable (fun ω => max (-(M ω)) 0) P)
    (hPosConv : ∀ᵐ ω ∂P, Tendsto
      (fun k => max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0)
      atTop (𝓝 (max (M ω) 0)))
    (hNegConv : ∀ᵐ ω ∂P, Tendsto
      (fun k => max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0)
      atTop (𝓝 (max (-(M ω)) 0)))
    (C : ℝ) (hC : 0 ≤ C)
    (hPos2 : ∀ k, Integrable (fun ω =>
      (max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0) ^ 2) P ∧
      (∫ ω, (max (stoppedValue (fun i : ℕ => f (e i)) (τk k) ω) 0) ^ 2 ∂P) ≤ C)
    (hNeg2 : ∀ k, Integrable (fun ω =>
      (max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0) ^ 2) P ∧
      (∫ ω, (max (-(stoppedValue (fun i : ℕ => f (e i)) (τk k) ω)) 0) ^ 2 ∂P) ≤ C)
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
  have hSplit : ∀ k,
      (∫ ω, max (Mk k ω) 0 ∂P) -
      (∫ ω, max (-(Mk k ω)) 0 ∂P) = 0 := by
    intro k
    calc
      _ = (∫ ω, max (Mk k ω) 0 - max (-(Mk k ω)) 0 ∂P) := by
        exact (integral_sub (hPosI k) (hNegI k)).symm
      _ = ∫ ω, Mk k ω ∂P := by
        congr 1
        funext ω
        exact max_zero_sub_max_neg_zero_eq_self (Mk k ω)
      _ = 0 := hCentre k
  exact avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
    X Mk M hPosMeas hNegMeas hPosMMeas hNegMMeas
    hPosConv hNegConv C hC hPos2 hNeg2 hSplit