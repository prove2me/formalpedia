-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_C1_with_power_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:31:10.784223+00:00
-- url     : https://prove2.me/submissions/faee7d16-1c99-4823-b3cb-bcd8455a08d7

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_antitone_power_product_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_signed_powers_exist_dominated
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_resolvent_from_envelope
import Mathlib.Analysis.Calculus.ContDiff.Defs
open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Retain signed-power domination and integrability in the C1 construction. -/
theorem solution
    (k κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkmeas : Measurable k)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hκanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hkdom : ∀ t : ℝ, 0 ≤ t → |k t| ≤ κ t)
    (hF0 : F 0 = κ)
    (hFrec : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFnonneg : ∀ n : ℕ, ∀ s : ℝ, 0 ≤ s → 0 ≤ F n s)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1))
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∃ (P : ℕ → ℝ → ℝ) (g : ℝ → ℝ),
      P 0 = k ∧
      (∀ n : ℕ, P (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x) ∧
      (g = fun y : ℝ => 1 / a + Real.exp (w * y) *
        (∑' n : ℕ, (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P n s ∂volume)) / a)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by
  have hprod : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s)
        volume 0 x :=
    causal_antitone_power_product_integrable κ F ρ hρ0 hκanti
      hκcont hκnonneg hκL1 hFL1
      (fun n s hs => hFnonneg n s (le_of_lt hs)) hFpoint
  obtain ⟨P, hP0, hPrec, hPL1, hPdom⟩ :=
    causal_l1_signed_powers_exist_dominated
      k κ F hkL1 hkmeas hkdom hF0 hFrec hprod
  obtain ⟨g, hg, hgc, hgC1⟩ :=
    causal_neumann_C1_resolvent_from_envelope
      k P F a ρ w ha hρ0 hρ1 hw hkL1 hkcont hkzero
      hP0 hPrec hPL1 hFL1 hPdom hFmass hFpoint
  exact ⟨P, g, hP0, hPrec, hPL1, hPdom, hg, hgc, hgC1⟩
