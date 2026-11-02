-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:15:23.22092+00:00
-- url     : https://prove2.me/submissions/8d7ece62-7ad6-40c6-938e-75535b3acbdb

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Exact finite-horizon payment domains stabilise pathwise under an
    arbitrary almost-surely divergent tail-infimum of source clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T =
        paymentTimes (ruinTime X x D ω) ∩ Iic T := by
  filter_upwards [hSliminfAE] with ω hω
  let r : ℝ≥0∞ := ENNReal.ofReal T
  have hr : r < ⊤ := ENNReal.ofReal_lt_top
  have hSome : ∃ N : ℕ, r < ⨅ k : ℕ, S (N + k) ω := by
    by_contra hnone
    have hle : ∀ n : ℕ, (⨅ k : ℕ, S (n + k) ω) ≤ r := by
      intro n
      exact le_of_not_gt (fun hn => hnone ⟨n, hn⟩)
    have hsup : (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) ≤ r := iSup_le hle
    rw [hω] at hsup
    exact (not_lt_of_ge hsup) hr
  rcases hSome with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hcap : ENNReal.ofReal T < S n ω := by
    calc
      ENNReal.ofReal T < ⨅ k : ℕ, S (N + k) ω := hN
      _ ≤ S (N + (n - N)) ω := iInf_le _ (n - N)
      _ = S n ω := by rw [Nat.add_sub_of_le hn]
  exact avram_wave6_original_zero_endpoint_finite_horizon_payment_domain_clip
    X x C D hD T hT (S n ω) hcap ω
end
