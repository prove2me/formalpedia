-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_renewal_density_l1_resolvent_for_any_recursion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:01:26.724183+00:00
-- url     : https://prove2.me/submissions/075c7844-1309-459c-a3e3-d665aeb47681

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_density_l1_resolvent

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (κ : ℝ → ℝ) (ρ : ℝ)
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
    IntegrableOn (fun x : ℝ => ∑' n : ℕ, G n x)
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, G n x ∂volume) =
      ρ / (1 - ρ) := by
  obtain ⟨F, h0, hrec, -, hI, hM⟩ :=
    AvramDividend.Classical.causal_subunit_renewal_density_l1_resolvent κ ρ hρpos hρlt hcont hanti
      hκzero hκpos hκL1 hmass
  have hFG : G = F := by
    funext n
    induction n with
    | zero => rw [hGzero, h0]
    | succ n ih => rw [hGrec, hrec, ih]
  rw [hFG]
  exact ⟨hI, hM⟩
