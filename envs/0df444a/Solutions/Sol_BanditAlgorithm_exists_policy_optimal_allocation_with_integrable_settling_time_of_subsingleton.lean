-- Prove2me | solution 1 for BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T20:22:52.644278+00:00
-- url     : https://prove2.me/submissions/3ef7ab7a-a1d9-4970-be7b-cf2ca2c23e14

import Theorems.Thm_BanditAlgorithm_settling_of_allocation_half_and_forced_exploration
import Theorems.Thm_BanditAlgorithm_exists_isOptimalAllocation_gaussian

/-!
# Proposition 13 when there is only one arm

`safePolicy`, the D-Tracking rule used when `k ≥ 2`, maximises
`min_{j ≠ î} …`, an infimum over an empty index set when `k = 1`; so the
degenerate case has to be supplied separately.  It is genuinely degenerate rather
than merely small: with one arm there is nothing to identify, `Fin k` is a
subsingleton, and **every** trajectory plays the only arm at every round.  No
measure theory is involved — the pull counts are `T_0(t) = t` identically.

Consequently the forced-exploration bound holds pointwise, and the empirical
allocation is `T_0(n)/n = 1` exactly from round one on, so the allocation half of
Proposition 13 has settling time `1`, not merely an integrable one.  Only the
empirical means need a genuine argument, and that is exactly what the imported
`settling_of_allocation_half_and_forced_exploration` supplies.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## A policy for the degenerate case -/

/-- The policy that always plays the same arm.  With one arm any policy would do;
this is the simplest measurable one. -/
noncomputable def constPolicySub (k : ℕ) [NeZero k] : BanditPolicy k where
  select _ := Kernel.const _ (Measure.dirac ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩)
  markov _ := by infer_instance

/-! ## Counts, deterministically -/

/-- With a single arm every round plays it, for every trajectory. -/
theorem trajPullCount_of_subsingleton (hk1 : ∀ i j : Fin k, i = j)
    (j : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : trajPullCount j t ω = t := by
  classical
  unfold trajPullCount
  have hfilter : (Finset.range t).filter (fun s ↦ (ω s).1 = j) = Finset.range t := by
    refine Finset.filter_true_of_mem fun s _ ↦ ?_
    exact hk1 _ _
  rw [hfilter, Finset.card_range]

/-- Hence the forced-exploration bound, with nothing to prove. -/
theorem forced_exploration_of_subsingleton [NeZero k] (hk1 : ∀ i j : Fin k, i = j)
    (t : ℕ) (j : Fin k) (ω : ℕ → Fin k × ℝ) :
    Real.sqrt (t : ℝ) - 2 * (k : ℝ) ≤ (trajPullCount j t ω : ℝ) := by
  rw [trajPullCount_of_subsingleton hk1 j t ω]
  have hsq : Real.sqrt (t : ℝ) ≤ (t : ℝ) + 1 := by
    rcases le_total (t : ℝ) 1 with h | h
    · have : Real.sqrt (t : ℝ) ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt h
      linarith
    · have hnn : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (t : ℝ),
        Real.sqrt_le_sqrt (show (t : ℝ) ≤ (t : ℝ) ^ 2 by nlinarith)]
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

/-! ## The allocation is exactly the point mass -/

/-- With a single arm the empirical allocation is `1` from round one on. -/
theorem trajAllocation_of_subsingleton (hk1 : ∀ i j : Fin k, i = j)
    (j : Fin k) {n : ℕ} (hn : 0 < n) (ω : ℕ → Fin k × ℝ) :
    trajAllocation j n ω = 1 := by
  have hrw : trajAllocation j n ω = (trajPullCount j n ω : ℝ) / (n : ℝ) := rfl
  rw [hrw, trajPullCount_of_subsingleton hk1 j n ω]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  field_simp

/-- With a single arm any probability vector is the point mass. -/
theorem eq_one_of_subsingleton_of_sum [NeZero k] (hk1 : ∀ i j : Fin k, i = j)
    {α : Fin k → ℝ≥0} (hsum : ∑ i, α i = 1) (j : Fin k) : (α j : ℝ) = 1 := by
  classical
  have huniv : (Finset.univ : Finset (Fin k)) = {j} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ j, fun l _ ↦ ?_⟩
    exact hk1 l j
  rw [huniv, Finset.sum_singleton] at hsum
  rw [hsum, NNReal.coe_one]

/-! ## Proposition 13, degenerately -/

/-- **Both halves of Proposition 13 for one arm.**  The allocation settles at
round one; only the means need the deviation bound, which the imported
`settling_of_allocation_half_and_forced_exploration` supplies. -/
theorem prop13_constPolicySub [NeZero k] (hk1 : ∀ i j : Fin k, i = j)
    (μvec : Fin k → ℝ) {α : Fin k → ℝ≥0} (hsum : ∑ i, α i = 1)
    {ξ : ℝ} (hξ : 0 < ξ) :
    (∀ᵐ ω ∂(banditTrajMeasure (gaussianBandit μvec) (constPolicySub k)),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (0 < n ∧ (∀ i, |trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
            (∀ i, |trajEmpiricalMean i n ω - μvec i| ≤ ξ)))
      ∧ ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
          (0 < n ∧ (∀ i, |trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
            (∀ i, |trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
        ∂(banditTrajMeasure (gaussianBandit μvec) (constPolicySub k)) ≠ ⊤ := by
  classical
  set P : Measure (ℕ → Fin k × ℝ) :=
    banditTrajMeasure (gaussianBandit μvec) (constPolicySub k) with hP
  -- the count bound, for every trajectory
  have hcount : ∀ᵐ ω ∂P, ∀ (t : ℕ) (j : Fin k),
      Real.sqrt (t : ℝ) - 2 * (k : ℝ) ≤ (trajPullCount j t ω : ℝ) :=
    Filter.Eventually.of_forall fun ω t j ↦ forced_exploration_of_subsingleton hk1 t j ω
  -- the allocation is accurate at every positive round, for every trajectory
  have hAacc : ∀ (n : ℕ), 0 < n → ∀ ω : ℕ → Fin k × ℝ,
      0 < n ∧ ∀ i, |trajAllocation i n ω - (α i : ℝ)| ≤ ξ := by
    intro n hn ω
    refine ⟨hn, fun j ↦ ?_⟩
    rw [trajAllocation_of_subsingleton hk1 j hn ω,
      eq_one_of_subsingleton_of_sum hk1 hsum j]
    simpa using hξ.le
  have hAsettle : ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (0 < n ∧ ∀ i, |trajAllocation i n ω - (α i : ℝ)| ≤ ξ) :=
    Filter.Eventually.of_forall fun ω ↦ ⟨1, fun n hn ↦ hAacc n (by omega) ω⟩
  -- and the failure series is a finite head
  have hAsum : ∑' m : ℕ, ((m : ℝ≥0∞) + 1) *
      P {ω : ℕ → Fin k × ℝ |
        0 < m ∧ ∀ i, |trajAllocation i m ω - (α i : ℝ)| ≤ ξ}ᶜ ≠ ⊤ := by
    have hzero : ∀ m : ℕ, ((m : ℝ≥0∞) + 1) *
        P {ω : ℕ → Fin k × ℝ |
            0 < m ∧ ∀ i, |trajAllocation i m ω - (α i : ℝ)| ≤ ξ}ᶜ
          = if m = 0 then ((0 : ℝ≥0∞) + 1) *
              P {ω : ℕ → Fin k × ℝ |
                0 < 0 ∧ ∀ i, |trajAllocation i 0 ω - (α i : ℝ)| ≤ ξ}ᶜ else 0 := by
      intro m
      by_cases hm : m = 0
      · rw [if_pos hm, hm]; norm_num
      · rw [if_neg hm]
        have hpos : 0 < m := Nat.pos_of_ne_zero hm
        have hempty : {ω : ℕ → Fin k × ℝ |
            0 < m ∧ ∀ i, |trajAllocation i m ω - (α i : ℝ)| ≤ ξ}ᶜ = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro ω hω
          exact hω (hAacc m hpos ω)
        rw [hempty, measure_empty, mul_zero]
    rw [tsum_congr hzero]
    have hsupp : ∀ m ∉ Finset.range 1,
        (if m = 0 then ((0 : ℝ≥0∞) + 1) *
          P {ω : ℕ → Fin k × ℝ |
            0 < 0 ∧ ∀ i, |trajAllocation i 0 ω - (α i : ℝ)| ≤ ξ}ᶜ else 0) = 0 := by
      intro m hm
      have hne : m ≠ 0 := by
        intro hc
        exact hm (Finset.mem_range.mpr (by omega))
      rw [if_neg hne]
    rw [tsum_eq_sum hsupp]
    refine (ENNReal.sum_lt_top.mpr fun m _ ↦ ?_).ne
    by_cases hm : m = 0
    · rw [if_pos hm]
      exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
    · rw [if_neg hm]; exact ENNReal.zero_lt_top
  exact settling_of_allocation_half_and_forced_exploration μvec (constPolicySub k)
    (fun j ↦ ((α j : ℝ))) hξ hcount hAsettle hAsum

end BanditAlgorithm

open BanditAlgorithm

theorem solution {k : ℕ} [NeZero k] (hk1 : ∀ i j : Fin k, i = j) :
    ∃ pol : BanditAlgorithm.BanditPolicy k,
      ∀ (μvec : Fin k → ℝ) (istar : Fin k),
        (∀ j, j ≠ istar → μvec j < μvec istar) →
        ∃ α : Fin k → NNReal,
          (∀ i, 0 < α i) ∧
          BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
              (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α ∧
          ∀ ξ : ℝ, 0 < ξ →
          (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol),
              ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))) ∧
            ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
              ∂(BanditAlgorithm.banditTrajMeasure
                (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤ := by
  classical
  refine ⟨constPolicySub k, fun μvec istar hstar ↦ ?_⟩
  obtain ⟨α, hαpos, hα⟩ := exists_isOptimalAllocation_gaussian hstar
  have hsum : ∑ i, α i = 1 := hα.1
  exact ⟨α, hαpos, hα, fun ξ hξ ↦ prop13_constPolicySub hk1 μvec hsum hξ⟩
