-- Prove2me | solution 1 for BanditAlgorithm.mdp_expected_reward_ge_of_reverse_bellman_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T15:10:54.96459+00:00
-- url     : https://prove2.me/submissions/c33ecf16-1070-4ab5-8894-5804c4e67bec

import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

/-!
Mirror image of the Bellman-inequality accumulation.  If `(ρ, v)` satisfies the
*reverse* inequality `ρ + v(s) ≤ r_{f(s)}(s) + ⟨P_{f(s)}(s), v⟩` along a fixed
deterministic memoryless policy `f`, then the same telescoping run backwards
shows that `f` collects at least `n ρ` minus the span of `v`.
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

/-- Under a deterministic memoryless policy the step kernel just appends the
action `f s` to the state `s`. -/
private lemma integral_stepKernel_det (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (f : Fin S → Fin A) (n : ℕ) (h : MDPTrajectory S A n) (G : Fin S × Fin A → ℝ) :
    ∫ p, G p ∂(mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h)
      = ∫ s, G (s, f s) ∂(mdpStateKernel M μ0 n h) := by
  rw [integral_stepKernel]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
  show ∫ a, G (s, a) ∂(Kernel.deterministic (fun p : MDPTrajectory S A n × Fin S ↦ f p.2)
      ((measurable_of_countable f).comp measurable_snd) (h, s)) = G (s, f s)
  rw [Kernel.deterministic_apply, integral_dirac]

/-- **The reverse Bellman inequality accumulates along its own policy.** -/
private lemma reward_add_nextValue_ge (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (f : Fin S → Fin A) (ρ : ℝ) (v : Fin S → ℝ)
    (hbell : ∀ s, ρ + v s ≤ M.r s (f s) + ∑ s', (M.P s (f s) s' : ℝ) * v s') (n : ℕ) :
    (n : ℝ) * ρ + ∫ s, v s ∂μ0.toMeasure
      ≤ ∫ h, (mdpTrajectoryReward M h + nextValue M μ0 v n h)
          ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) n) := by
  induction n with
  | zero =>
      rw [mdpMeasure, integral_dirac]
      simp [mdpTrajectoryReward, nextValue, mdpStateKernel]
  | succ n ih =>
      push_cast
      have key : ∀ h : MDPTrajectory S A n,
          mdpTrajectoryReward M h + nextValue M μ0 v n h + ρ
            ≤ ∫ p, (mdpTrajectoryReward M (Fin.snoc h p)
                  + nextValue M μ0 v (n + 1) (Fin.snoc h p))
                ∂(mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h) := by
        intro h
        have hpt : ∀ s : Fin S,
            (mdpTrajectoryReward M h + ρ) + v s
              ≤ mdpTrajectoryReward M (Fin.snoc h (s, f s))
                  + nextValue M μ0 v (n + 1) (Fin.snoc h (s, f s)) := by
          intro s
          rw [trajectoryReward_snoc, nextValue_succ]
          have := hbell s
          simp only []
          linarith
        calc mdpTrajectoryReward M h + nextValue M μ0 v n h + ρ
            = ∫ s, ((mdpTrajectoryReward M h + ρ) + v s) ∂(mdpStateKernel M μ0 n h) := by
              rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const,
                probReal_univ, smul_eq_mul, one_mul, ← nextValue]
              ring
          _ ≤ ∫ s, (mdpTrajectoryReward M (Fin.snoc h (s, f s))
                  + nextValue M μ0 v (n + 1) (Fin.snoc h (s, f s)))
                ∂(mdpStateKernel M μ0 n h) :=
              integral_mono Integrable.of_finite Integrable.of_finite hpt
          _ = ∫ p, (mdpTrajectoryReward M (Fin.snoc h p)
                  + nextValue M μ0 v (n + 1) (Fin.snoc h p))
                ∂(mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h) :=
              (integral_stepKernel_det M μ0 f n h
                (fun p ↦ mdpTrajectoryReward M (Fin.snoc h p)
                  + nextValue M μ0 v (n + 1) (Fin.snoc h p))).symm
      calc ((n : ℝ) + 1) * ρ + ∫ s, v s ∂μ0.toMeasure
          = ((n : ℝ) * ρ + ∫ s, v s ∂μ0.toMeasure) + ρ := by ring
        _ ≤ (∫ h, (mdpTrajectoryReward M h + nextValue M μ0 v n h)
              ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) n)) + ρ := by linarith
        _ = ∫ h, (mdpTrajectoryReward M h + nextValue M μ0 v n h + ρ)
              ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) n) := by
            rw [eq_comm, integral_add Integrable.of_finite Integrable.of_finite, integral_const,
              probReal_univ, smul_eq_mul, one_mul]
        _ ≤ ∫ h, (∫ p, (mdpTrajectoryReward M (Fin.snoc h p)
                + nextValue M μ0 v (n + 1) (Fin.snoc h p))
              ∂(mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h))
              ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) n) :=
            integral_mono Integrable.of_finite Integrable.of_finite key
        _ = ∫ h, (mdpTrajectoryReward M h + nextValue M μ0 v (n + 1) h)
              ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) (n + 1)) :=
            (BanditAlgorithm.mdp_integral_trajectory_succ M μ0 (mdpMemorylessDetPolicy f) n
              (fun h ↦ mdpTrajectoryReward M h + nextValue M μ0 v (n + 1) h)).symm

/-- **The finite-horizon consequence of the reverse Bellman inequality**
(L&S §38.2, the optimality half of Theorem 38.2): the memoryless deterministic
policy `f` collects at least `n ρ` minus the span of `v`. -/
theorem solution (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (f : Fin S → Fin A) (ρ : ℝ) (v : Fin S → ℝ)
    (lo hi : ℝ) (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s, ρ + v s ≤ M.r s (f s) + ∑ s', (M.P s (f s) s' : ℝ) * v s') (n : ℕ) :
    (n : ℝ) * ρ - (hi - lo)
      ≤ mdpExpectedReward M μ0 (mdpMemorylessDetPolicy f) n := by
  have hkey := reward_add_nextValue_ge M μ0 f ρ v hbell n
  rw [integral_add Integrable.of_finite Integrable.of_finite] at hkey
  have hμ0 : lo ≤ ∫ s, v s ∂μ0.toMeasure := by
    calc lo = ∫ _s, lo ∂μ0.toMeasure := by
          rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ ≤ _ := integral_mono Integrable.of_finite Integrable.of_finite fun s ↦ (hv s).1
  have hnext : (∫ h, nextValue M μ0 v n h
      ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) n)) ≤ hi := by
    have hpt : ∀ h : MDPTrajectory S A n, nextValue M μ0 v n h ≤ hi := by
      intro h
      calc nextValue M μ0 v n h ≤ ∫ _s, hi ∂(mdpStateKernel M μ0 n h) :=
            integral_mono Integrable.of_finite Integrable.of_finite fun s ↦ (hv s).2
        _ = hi := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    calc (∫ h, nextValue M μ0 v n h ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) n))
        ≤ ∫ _h, hi ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) n) :=
          integral_mono Integrable.of_finite Integrable.of_finite hpt
      _ = hi := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [mdpExpectedReward]
  linarith
