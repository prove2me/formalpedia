-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_postPayment_condExp_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:09:18.065711+00:00
-- url     : https://prove2.me/submissions/9384fd1d-7091-4faa-877b-72e9465496fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_integrable_adapted_reserve_lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Conditional original-Lévy future reward from the actual post-payment
    reserve, with conditioning in the right-continuous dividend history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t)
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ y : ℝ, Integrable
      (fun η => f (y + X.X (t - s) η)) P)
    (hZm : Measurable (fun ω => x + X.X s ω - rightLimit D s ω))
    (hZI : Integrable (fun ω => x + X.X s ω - rightLimit D s ω) P)
    (hZPay : Integrable (fun ω =>
      f (x + X.X s ω - rightLimit D s ω +
        (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω =>
      f ((SimpleFunc.approxOn
        (fun η => x + X.X s η - rightLimit D s η) hZm
        (Set.range (fun η => x + X.X s η - rightLimit D s η) ∪ {0})
        0 (by simp) n) ω + (X.X t ω - X.X s ω))) P) :
    P[(fun η => f (x + X.X s η - rightLimit D s η +
      (X.X t η - X.X s η))) | 𝓕.rightCont s] =ᵐ[P]
    (fun ω => ∫ η, f (x + X.X s ω - rightLimit D s ω +
      X.X (t - s) η) ∂P) := by
  obtain ⟨Y, hpath, -, -, -⟩ := levy_rightCont_process X
  have hadapt : Measurable[𝓕.rightCont s]
      (fun ω => x + X.X s ω - rightLimit D s ω) :=
    (postPaymentReserve_cadlag_adapted X x D hD).2.2 s
  have hkernel := levy_increment_condExp_integrable_adapted_reserve_lipschitz
    Y s t hst f hf L hL hLip
    (by simpa only [hpath] using hInt)
    (fun ω => x + X.X s ω - rightLimit D s ω)
    hadapt hZm hZI
    (by simpa only [hpath] using hZPay)
    (by simpa only [hpath] using hSPay)
  simpa only [hpath] using hkernel
