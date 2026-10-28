-- Prove2me | solution 2 for AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:04:29.097176+00:00
-- url     : https://prove2.me/submissions/4a2a66cf-1687-4ce9-8d80-a7220a46ce6d

import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_at_zero

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (κ : ℝ → ℝ) (ρ b : ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ κ x)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hmass : (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ)
    (G : ℕ → ℝ → ℝ)
    (hGzero : G 0 = κ)
    (hGrec : ∀ n : ℕ, G (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * G n (x - y) ∂volume) :
    ContinuousOn
      (fun x : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else G (n - 1) x)
      (Ioi (0 : ℝ)) ∧
    (∀ x : ℝ, 0 < x →
      IntervalIntegrable
        (fun y : ℝ => b * ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else G (n - 1) y)
        volume 0 x) := by
  obtain ⟨F, h0, hrec, hC, hI⟩ :=
    AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_at_zero κ ρ b
      hρpos hρlt hcont hanti hκzero hκpos hκL1 hmass
  have hFG : G = F := by
    funext n
    induction n with
    | zero => rw [hGzero, h0]
    | succ n ih => rw [hGrec, hrec, ih]
  rw [hFG]
  exact ⟨hC, hI⟩
