-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:03:17.026053+00:00
-- url     : https://prove2.me/submissions/f819b6f1-45c1-410c-8417-0c338d4a69fc

import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Every causal subunit convolution recursion yields the same regular shifted density. -/
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
  obtain ⟨F, hFzero, hFrec, hContinuous, hInt⟩ :=
    causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
      κ ρ b hρpos hρlt hcont hanti hκzero hκpos hκL1 hmass
  have hGF : ∀ n : ℕ, G n = F n := by
    intro n
    induction n with
    | zero => rw [hGzero, hFzero]
    | succ n ih =>
      rw [hGrec n, hFrec n, ih]
  have heq (x : ℝ) :
      (∑' n : ℕ, if n = 0 then (0 : ℝ) else G (n - 1) x) =
        ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) x := by
    congr 1
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, hGF]
  have hfun :
      (fun x : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else G (n - 1) x) =
      (fun x : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) x) :=
    funext heq
  refine ⟨?_, ?_⟩
  · simpa only [hfun] using hContinuous
  · intro x hx
    simpa only [heq] using hInt x hx