-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_for_any_recursion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:37:25.531023+00:00
-- url     : https://prove2.me/submissions/c4eb8e92-ad9c-49f0-9ebc-3d8f7205c883

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_interval_integrable_at_zero
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ κ x)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ)
    (F : ℕ → ℝ → ℝ)
    (hFzero : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y)
        volume 0 x := by
  obtain ⟨G, hG0, hGs, -, -, -, hI⟩ :=
    AvramDividend.Classical.causal_subunit_renewal_density_interval_integrable_at_zero κ ρ hρpos
      hρlt hcont hanti hκzero hκpos hκL1 hmass
  have hFG : F = G := by
    funext n
    induction n with
    | zero => rw [hFzero, hG0]
    | succ n ih => rw [hFsucc, hGs, ih]
  rw [hFG]
  exact hI
