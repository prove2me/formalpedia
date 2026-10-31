-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_postPayment_source_oneStep_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:21:15.897991+00:00
-- url     : https://prove2.me/submissions/20aed74f-a01b-482e-82b9-6af1ba43b349

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_one_step_dividend_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Source dividend atom plus the future original-Lévy payoff obeys the
    right-continuous conditional cash budget under exact HJB step premises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t)
    (w : ℝ → ℝ) (hw : Measurable w) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (hInt : ∀ y : ℝ, Integrable (fun η => w (y + X.X (t - s) η)) P)
    (q : ℝ)
    (hZm : Measurable (fun ω =>
      (x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω)))
    (hZI : Integrable (fun ω =>
      (x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω)) P)
    (hZPay : Integrable (fun ω => w
      ((x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω) +
        (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω => w
      ((SimpleFunc.approxOn
        (fun η => (x + X.X s η - D s η) -
          (rightLimit D s η - D s η)) hZm
        (Set.range (fun η => (x + X.X s η - D s η) -
          (rightLimit D s η - D s η)) ∪ {0})
        0 (by simp) n) ω + (X.X t ω - X.X s ω))) P)
    (hsec : ∀ᵐ ω ∂P, rightLimit D s ω - D s ω ≤
      w (x + X.X s ω - D s ω) -
      w ((x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω)))
    (hsemi : ∀ᵐ ω ∂P,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ η, w ((x + X.X s ω - D s ω) -
          (rightLimit D s ω - D s ω) + X.X (t - s) η) ∂P) ≤
      w ((x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω))) :
    ∀ᵐ ω ∂P, (rightLimit D s ω - D s ω) +
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (P[(fun η => w
          ((x + X.X s η - D s η) - (rightLimit D s η - D s η) +
            (X.X t η - X.X s η))) | 𝓕.rightCont s]) ω ≤
      w (x + X.X s ω - D s ω) := by
  obtain ⟨Y, hpath, -, -, -⟩ := levy_rightCont_process X
  have hsame :
      (fun ω => (x + X.X s ω - D s ω) -
        (rightLimit D s ω - D s ω)) =
      (fun ω => x + X.X s ω - rightLimit D s ω) := by
    funext ω
    ring
  have hadapt : Measurable[𝓕.rightCont s]
      (fun ω => (x + X.X s ω - D s ω) -
        (rightLimit D s ω - D s ω)) := by
    rw [hsame]
    exact (postPaymentReserve_cadlag_adapted X x D hD).2.2 s
  have hIntY : ∀ y : ℝ,
      Integrable (fun η => w (y + Y.X (t - s) η)) P := by
    simpa only [hpath] using hInt
  have hsemiY : ∀ᵐ ω ∂P,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ η, w ((x + X.X s ω - D s ω) -
          (rightLimit D s ω - D s ω) + Y.X (t - s) η) ∂P) ≤
      w ((x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω)) := by
    simpa only [hpath] using hsemi
  have hbudget := levy_adapted_reserve_one_step_dividend_budget
    Y s t hst w hw L hL hLip
    hIntY
    (fun ω => x + X.X s ω - D s ω)
    (fun ω => rightLimit D s ω - D s ω) q
    hadapt hZm hZI
    (by simpa only [hpath] using hZPay)
    (by simpa only [hpath] using hSPay)
    hsec hsemiY
  simpa only [hpath] using hbudget
