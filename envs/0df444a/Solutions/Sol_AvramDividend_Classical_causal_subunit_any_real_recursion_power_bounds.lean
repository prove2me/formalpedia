-- Prove2me | solution 1 for AvramDividend.Classical.causal_subunit_any_real_recursion_power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:49:29.244105+00:00
-- url     : https://prove2.me/submissions/0861e0a4-131b-4ded-bff3-49b6481c2f26

import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Every exact convolution recursion has the canonical L1, positivity and geometric bounds. -/
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
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) := by
  obtain ⟨hkint, G, hGzero, hGsucc, hGL1, hGpos, hGbound⟩ :=
    causal_subunit_renewal_full_real_power_package
      k ρ hρpos hρlt hcont hanti hkzero hkpos hkL1 hmass
  have hFG : F = G := by
    funext n
    induction n with
    | zero =>
        rw [hFzero, hGzero]
    | succ n ih =>
        rw [hFsucc n, hGsucc n, ih]
  subst F
  exact ⟨hkint, hGL1, hGpos, hGbound⟩
