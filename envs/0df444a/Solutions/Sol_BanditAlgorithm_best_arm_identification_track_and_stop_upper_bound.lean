-- Prove2me | solution 1 for BanditAlgorithm.best_arm_identification_track_and_stop_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T14:31:40.819089+00:00
-- url     : https://prove2.me/submissions/957a13a6-d2ea-48a1-a555-12ad22e30974

import Theorems.Thm_BanditAlgorithm_chernoff_stopping_rule_sound
import Theorems.Thm_BanditAlgorithm_chernoff_stopping_time_sample_complexity_of_settling
import Theorems.Thm_BanditAlgorithm_exists_policy_optimal_allocation_with_integrable_settling_time

/-!
# The upper half of Theorem 33.6, assembled from its three ingredients

Track-and-Stop (L&S Algorithm 21) factors into three independent statements, and
the assembly consumes each exactly once:

* `chernoff_stopping_rule_sound` — **L&S Lemma 33.7.**  Chernoff's stopping rule
  with the threshold `β_t(δ) = k log(t² + t) + f⁻¹(δ)` is `δ`-sound for *every*
  `δ` and *whatever* the sampling rule.  This is what keeps the leading constant
  exact: the general exponential-family analogue (Garivier–Kaufmann
  Proposition 12) needs `α > 1` and would deliver only `α · c*(ν)`.
* `exists_policy_optimal_allocation_with_integrable_settling_time` —
  **Garivier–Kaufmann Proposition 13.**  There is one sampling rule, fixed before
  the environment and before `δ`, whose empirical allocation and means settle to
  an optimal allocation with an *integrable* settling time.
* `chernoff_stopping_time_sample_complexity_of_settling` — **Theorem 14.**  Given
  that, `E[τ_δ]` is finite and its normalised limit superior is at most `c*(ν)`.

## Why the sampling rule carries a quantitative guarantee

An earlier version of this decomposition asked only for almost-sure convergence
of the empirical allocation.  That is not enough, and the node asserting the
sample-complexity bound from it has been retired: a rule may delay its second arm
to a round `M` that is almost surely finite but has `E[M] = ∞`, and while an arm
is unplayed the statistic carries the factor `T_î T_j/(T_î + T_j) = 0` and cannot
cross any threshold, so `τ_δ ≥ M` uniformly in `δ`.  The integrable settling time
is the quantitative input that rules this out, and it is where D-Tracking's
forced exploration is actually used.

## The order of the quantifiers

The sampling rule is chosen before `δ`, as the statement demands: Algorithm 21's
tracking step does not consult the confidence level, only the stopping threshold
does.  Note also that the environment is *not* fixed before the policy — one
policy serves the whole Gaussian class — which is why the middle ingredient is
stated as a single existential over policies with a universal over parameter
vectors inside, and not the other way round.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-! ## "Unique optimal arm" as a strict maximiser

`Def_BanditTrajectory` phrases uniqueness of the best arm as
`∃! i, i ∈ banditOptimalArms ν`, whereas the Gaussian computations want the
strict order `∀ j ≠ i*, μ_j < μ_{i*}`.  For the Gaussian class the two agree. -/

theorem banditArmMean_gaussianBandit' (μvec : Fin k → ℝ) (i : Fin k) :
    banditArmMean (gaussianBandit μvec) i = μvec i := by
  simp [banditArmMean, gaussianBandit, integral_id_gaussianReal]

theorem banditOptimalMean_gaussianBandit' (μvec : Fin k → ℝ) :
    banditOptimalMean (gaussianBandit μvec) = ⨆ i, μvec i := by
  simp [banditOptimalMean, banditArmMean_gaussianBandit']

theorem banditOptimalArms_gaussianBandit' (μvec : Fin k → ℝ) :
    banditOptimalArms (gaussianBandit μvec) = {i | μvec i = ⨆ j, μvec j} := by
  ext i
  simp [banditOptimalArms, banditArmMean_gaussianBandit', banditOptimalMean_gaussianBandit']

theorem mem_banditOptimalArms_gaussianBandit_iff' (μvec : Fin k → ℝ) (i : Fin k) :
    i ∈ banditOptimalArms (gaussianBandit μvec) ↔ ∀ j, μvec j ≤ μvec i := by
  rw [banditOptimalArms_gaussianBandit']
  constructor
  · intro hi j
    rw [Set.mem_setOf_eq] at hi
    exact hi ▸ le_ciSup (f := μvec) (Finite.bddAbove_range _) j
  · intro hi
    exact le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) (ciSup_le hi)

/-- A unique optimal arm of a Gaussian bandit is a strict maximiser. -/
theorem exists_strict_max_of_existsUnique_optimal' {μvec : Fin k → ℝ}
    (h : ∃! i, i ∈ banditOptimalArms (gaussianBandit μvec)) :
    ∃ istar : Fin k, ∀ j, j ≠ istar → μvec j < μvec istar := by
  obtain ⟨istar, hmem, huniq⟩ := h
  refine ⟨istar, fun j hj ↦ ?_⟩
  rw [mem_banditOptimalArms_gaussianBandit_iff'] at hmem
  by_contra hcon
  push_neg at hcon
  have hjmax : j ∈ banditOptimalArms (gaussianBandit μvec) := by
    rw [mem_banditOptimalArms_gaussianBandit_iff']
    intro l
    exact le_trans (hmem l) hcon
  exact hj (huniq j hjmax)

end BanditAlgorithm

open BanditAlgorithm

theorem solution {k : ℕ} (hk : 0 < k) :
    ∃ (π : BanditPolicy k) (τ : ℝ → (ℕ → Fin k × ℝ) → ℕ∞)
      (ψ : ℝ → (ℕ → Fin k × ℝ) → Fin k),
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        ∃ hτ : IsBanditStoppingTime (τ δ),
          Measurable[hτ.measurableSpace] (ψ δ) ∧
            IsSoundBAI δ π (τ δ) (ψ δ) (Set.range (gaussianBandit (k := k)))) ∧
      ∀ ν ∈ Set.range (gaussianBandit (k := k)), (∃! i, i ∈ banditOptimalArms ν) →
        (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
            ∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂banditTrajMeasure ν π ≠ ⊤) ∧
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂banditTrajMeasure ν π).toReal / Real.log (1 / δ)
                ≤ (baiComplexity ν (Set.range (gaussianBandit (k := k)))).toReal + ε := by
  haveI : NeZero k := ⟨hk.ne'⟩
  -- the sampling rule, with its Proposition 13 guarantee
  obtain ⟨π, hπ⟩ :=
    exists_policy_optimal_allocation_with_integrable_settling_time (k := k)
  refine ⟨π, fun δ ↦ chernoffStoppingTime (k := k) δ,
    fun δ ↦ chernoffRecommendation (k := k) δ, ?_, ?_⟩
  · -- soundness, at every confidence level
    intro δ hδ
    exact chernoff_stopping_rule_sound δ hδ π
  · -- finiteness and the asymptotic bound
    rintro ν ⟨μvec, rfl⟩ huniq
    obtain ⟨istar, hstar⟩ := exists_strict_max_of_existsUnique_optimal' huniq
    obtain ⟨α, hαpos, hopt, hsettle⟩ := hπ μvec istar hstar
    exact chernoff_stopping_time_sample_complexity_of_settling π μvec hstar α hαpos
      hopt hsettle
