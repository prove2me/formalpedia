-- Prove2me | solution 1 for BanditAlgorithm.mdp_expected_reward_le_of_bellman_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T04:33:09.399583+00:00
-- url     : https://prove2.me/submissions/9e580d7a-417b-4b5a-81c9-16468db0206f

import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

/-!
The Bellman inequality `r_a(s) + ⟨P_a(s), v⟩ ≤ ρ + v(s)` makes the process
`∑_{t ≤ T} r_{A_t}(S_t) + v(S_{T+1}) − T ρ` a supermartingale in expectation.
Accumulating it over the horizon and discarding the terminal value costs only
the span of `v`.
-/

variable {S A : ℕ}

/-- The integral against the measure of a probability vector is the
corresponding finite sum. -/
private lemma integral_stateDist (d : MDPStateDistribution S) (f : Fin S → ℝ) :
    ∫ s, f s ∂d.toMeasure = ∑ s, (d.prob s : ℝ) * f s := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have : d.toMeasure {s} = (d.prob s : ℝ≥0∞) := by
    simp only [MDPStateDistribution.toMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton s), Set.indicator_apply,
      Set.mem_singleton_iff]
    rw [Finset.sum_eq_single s] <;> simp +contextual
  rw [measureReal_def, this, smul_eq_mul]
  simp

/-- The step kernel integrates by first drawing the state, then the action. -/
private lemma integral_stepKernel (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) (h : MDPTrajectory S A n)
    (G : Fin S × Fin A → ℝ) :
    ∫ p, G p ∂(mdpStepKernel M μ0 π n h)
      = ∫ s, (∫ a, G (s, a) ∂(π.select n (h, s))) ∂(mdpStateKernel M μ0 n h) :=
  ProbabilityTheory.integral_compProd Integrable.of_finite

/-- The expected value of the state of the next round, given the trajectory so
far: `⟨P_{A_t}(S_t), v⟩`, and `⟨μ0, v⟩` at the start of the interaction. -/
private noncomputable def nextValue (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (v : Fin S → ℝ) (n : ℕ) (h : MDPTrajectory S A n) : ℝ :=
  ∫ s, v s ∂(mdpStateKernel M μ0 n h)

private lemma nextValue_succ (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (v : Fin S → ℝ) (n : ℕ) (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    nextValue M μ0 v (n + 1) (Fin.snoc h p) = ∑ s', (M.P p.1 p.2 s' : ℝ) * v s' := by
  rw [nextValue, mdpStateKernel, Kernel.comap_apply]
  simp only [Fin.snoc_last]
  show ∫ s, v s ∂((M.transitionDist p.1 p.2).toMeasure) = _
  rw [integral_stateDist]
  rfl

private lemma trajectoryReward_snoc (M : FiniteMDP S A) {n : ℕ}
    (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    mdpTrajectoryReward M (Fin.snoc h p) = mdpTrajectoryReward M h + M.r p.1 p.2 := by
  rw [mdpTrajectoryReward, mdpTrajectoryReward, Fin.sum_univ_castSucc]
  simp

private lemma integral_nextValue_step (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (v : Fin S → ℝ) (n : ℕ) (h : MDPTrajectory S A n) :
    ∫ p, v p.1 ∂(mdpStepKernel M μ0 π n h) = nextValue M μ0 v n h := by
  rw [integral_stepKernel, nextValue]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s ↦ by simp)

/-- The Bellman inequality accumulates along the interaction: the expected
reward of `n` rounds plus the expected value of the state reached after them is
at most `n ρ + ⟨μ0, v⟩`. -/
private lemma reward_add_nextValue_le (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (ρ : ℝ) (v : Fin S → ℝ)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) (n : ℕ) :
    ∫ h, (mdpTrajectoryReward M h + nextValue M μ0 v n h) ∂(mdpMeasure M μ0 π n)
      ≤ n * ρ + ∫ s, v s ∂μ0.toMeasure := by
  induction n with
  | zero =>
      rw [mdpMeasure, integral_dirac]
      simp [mdpTrajectoryReward, nextValue, mdpStateKernel]
  | succ n ih =>
      have key : ∀ h : MDPTrajectory S A n,
          (∫ p, (mdpTrajectoryReward M (Fin.snoc h p)
                + nextValue M μ0 v (n + 1) (Fin.snoc h p))
              ∂(mdpStepKernel M μ0 π n h))
            ≤ mdpTrajectoryReward M h + nextValue M μ0 v n h + ρ := by
        intro h
        have hpt : ∀ p : Fin S × Fin A,
            mdpTrajectoryReward M (Fin.snoc h p)
                + nextValue M μ0 v (n + 1) (Fin.snoc h p)
              ≤ (mdpTrajectoryReward M h + ρ) + v p.1 := by
          intro p
          rw [trajectoryReward_snoc, nextValue_succ]
          have := hbell p.1 p.2
          linarith
        calc (∫ p, (mdpTrajectoryReward M (Fin.snoc h p)
                  + nextValue M μ0 v (n + 1) (Fin.snoc h p))
                ∂(mdpStepKernel M μ0 π n h))
            ≤ ∫ p, ((mdpTrajectoryReward M h + ρ) + v p.1)
                ∂(mdpStepKernel M μ0 π n h) :=
              integral_mono Integrable.of_finite Integrable.of_finite hpt
          _ = (mdpTrajectoryReward M h + ρ) + nextValue M μ0 v n h := by
              rw [integral_add Integrable.of_finite Integrable.of_finite,
                integral_nextValue_step, integral_const, probReal_univ,
                smul_eq_mul, one_mul]
          _ = mdpTrajectoryReward M h + nextValue M μ0 v n h + ρ := by ring
      calc ∫ h, (mdpTrajectoryReward M h + nextValue M μ0 v (n + 1) h)
              ∂(mdpMeasure M μ0 π (n + 1))
          = ∫ h, (∫ p, (mdpTrajectoryReward M (Fin.snoc h p)
                + nextValue M μ0 v (n + 1) (Fin.snoc h p))
              ∂(mdpStepKernel M μ0 π n h)) ∂(mdpMeasure M μ0 π n) :=
            BanditAlgorithm.mdp_integral_trajectory_succ _ _ _ _ _
        _ ≤ ∫ h, (mdpTrajectoryReward M h + nextValue M μ0 v n h + ρ)
              ∂(mdpMeasure M μ0 π n) :=
            integral_mono Integrable.of_finite Integrable.of_finite key
        _ = (∫ h, (mdpTrajectoryReward M h + nextValue M μ0 v n h)
              ∂(mdpMeasure M μ0 π n)) + ρ := by
            rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const,
              probReal_univ, smul_eq_mul, one_mul]
        _ ≤ (n * ρ + ∫ s, v s ∂μ0.toMeasure) + ρ := by linarith
        _ = (n + 1 : ℕ) * ρ + ∫ s, v s ∂μ0.toMeasure := by push_cast; ring

/-- **The finite-horizon consequence of the Bellman inequality** (L&S §38.2,
the estimate behind Theorem 38.2): a pair `(ρ, v)` satisfying
`r_a(s) + ⟨P_a(s), v⟩ ≤ ρ + v(s)` caps the expected reward of every policy over
every horizon by `n ρ` plus the span of `v`. -/
theorem solution (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (ρ : ℝ) (v : Fin S → ℝ)
    (lo hi : ℝ) (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) (n : ℕ) :
    mdpExpectedReward M μ0 π n ≤ n * ρ + (hi - lo) := by
  have hkey := reward_add_nextValue_le M μ0 π ρ v hbell n
  rw [integral_add Integrable.of_finite Integrable.of_finite] at hkey
  have hμ0 : ∫ s, v s ∂μ0.toMeasure ≤ hi := by
    calc ∫ s, v s ∂μ0.toMeasure ≤ ∫ _s, hi ∂μ0.toMeasure :=
          integral_mono Integrable.of_finite Integrable.of_finite fun s ↦ (hv s).2
      _ = hi := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hnext : lo ≤ ∫ h, nextValue M μ0 v n h ∂(mdpMeasure M μ0 π n) := by
    have hpt : ∀ h : MDPTrajectory S A n, lo ≤ nextValue M μ0 v n h := by
      intro h
      calc lo = ∫ _s, lo ∂(mdpStateKernel M μ0 n h) := by
            rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
        _ ≤ nextValue M μ0 v n h :=
            integral_mono Integrable.of_finite Integrable.of_finite fun s ↦ (hv s).1
    calc lo = ∫ _h, lo ∂(mdpMeasure M μ0 π n) := by
          rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ ≤ _ := integral_mono Integrable.of_finite Integrable.of_finite hpt
  rw [mdpExpectedReward]
  linarith
