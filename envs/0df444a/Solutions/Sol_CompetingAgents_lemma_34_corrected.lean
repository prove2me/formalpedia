-- Prove2me | solution 1 for CompetingAgents.lemma_34_corrected
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:29:06.550122+00:00
-- url     : https://prove2.me/submissions/12eed37a-08ba-4e2a-8d73-a705663e6aab

import Mathlib
import Definitions.Def_CompetingAgents_thresholdProcess

open scoped NNReal

open CompetingAgents in
theorem solution {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (M : Model d ι) (β : Cov d) (n : ℕ) (S0 : ℝ) {Ω : Type*} (A : ℕ → Fin n → Ω → ι × Cov d)
    (κ : ℝ≥0) (hκ : LipschitzWith κ (eqMap M β)) (sβ : ℝ) (hsβ : sβ = eqMap M β sβ)
    (t : ℕ) (ω : Ω) :
    |thresholdProcess M β n S0 A t ω - sβ| ≤
      ∑ i ∈ Finset.range t, (κ : ℝ) ^ i *
        |thresholdProcess M β n S0 A (t - i) ω -
          eqMap M β (thresholdProcess M β n S0 A (t - (i + 1)) ω)| +
      (κ : ℝ) ^ t * |S0 - sβ| := by
  have hκ0 : (0 : ℝ) ≤ κ := κ.2
  induction t with
  | zero => simp [thresholdProcess]
  | succ t ih =>
    rw [Finset.sum_range_succ']
    have hre : ∑ i ∈ Finset.range t, (κ : ℝ) ^ (i + 1) *
        |thresholdProcess M β n S0 A (t + 1 - (i + 1)) ω -
          eqMap M β (thresholdProcess M β n S0 A (t + 1 - (i + 1 + 1)) ω)| =
        (κ : ℝ) * ∑ i ∈ Finset.range t, (κ : ℝ) ^ i *
          |thresholdProcess M β n S0 A (t - i) ω -
            eqMap M β (thresholdProcess M β n S0 A (t - (i + 1)) ω)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : t + 1 - (i + 1) = t - i := by omega
      have h2 : t + 1 - (i + 1 + 1) = t - (i + 1) := by omega
      rw [h1, h2, pow_succ]
      ring
    rw [hre]
    simp only [pow_zero, one_mul, Nat.sub_zero, zero_add, Nat.add_sub_cancel]
    have hL : |eqMap M β (thresholdProcess M β n S0 A t ω) - sβ| ≤
        κ * |thresholdProcess M β n S0 A t ω - sβ| := by
      have := hκ.dist_le_mul (thresholdProcess M β n S0 A t ω) sβ
      rw [Real.dist_eq, Real.dist_eq, ← hsβ] at this
      exact this
    have htri := abs_sub_le (thresholdProcess M β n S0 A (t + 1) ω)
      (eqMap M β (thresholdProcess M β n S0 A t ω)) sβ
    have h3 : (κ : ℝ) ^ (t + 1) * |S0 - sβ| = κ * ((κ : ℝ) ^ t * |S0 - sβ|) := by ring
    rw [h3]
    have h4 := mul_le_mul_of_nonneg_left ih hκ0
    linarith
