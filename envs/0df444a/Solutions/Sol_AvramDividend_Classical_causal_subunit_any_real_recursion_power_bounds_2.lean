-- Prove2me | solution 2 for AvramDividend.Classical.causal_subunit_any_real_recursion_power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:50:28.683996+00:00
-- url     : https://prove2.me/submissions/9453e561-9a33-43fd-bb3a-4215c4a02925

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package

open AvramDividend.Classical MeasureTheory Set


theorem solution
    (k : ℝ → ℝ) (ρ : ℝ) (F : ℕ → ℝ → ℝ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hanti : AntitoneOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ t : ℝ, t ≤ 0 → k t = 0)
    (hkpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ k t)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hmass : (∫ t in Ioi (0 : ℝ), k t ∂volume) = ρ)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume) :
    Integrable k volume ∧
    (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
    (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
    (∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)  := by 
  obtain ⟨hk, G, hG0, hGs, hGi, hGp, hGb⟩ :=
    causal_subunit_renewal_full_real_power_package k ρ hρpos hρlt hcont hanti hkzero hkpos hkL1 hmass
  have hFG : ∀ n, F n = G n := by
    intro n
    induction n with
    | zero => rw [hFzero, hG0]
    | succ n ih => rw [hFsucc n, hGs n, ih]
  refine ⟨hk, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · rw [hFG n]; exact hGi n
  · rw [hFG n]; exact hGp n
  · rw [hFG n]; exact hGb n
