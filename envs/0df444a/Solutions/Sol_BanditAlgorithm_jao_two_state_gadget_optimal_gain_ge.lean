-- Prove2me | solution 1 for BanditAlgorithm.jao_two_state_gadget_optimal_gain_ge
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T18:49:11.396063+00:00
-- url     : https://prove2.me/submissions/4f9956df-4d58-4f28-b092-1e858f2b9684

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Algebra.Field.GeomSum
import Definitions.Def_UCRL2ConfidenceSets
import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace JaoGain

/-- The indicator of the rewarding state `s_p = 1`. -/
def ind1s : Fin 2 → ℝ := fun s => if s = 1 then 1 else 0

lemma fin2_cases (s : Fin 2) : s = 0 ∨ s = 1 := by
  have hlt := s.isLt
  rcases Nat.eq_zero_or_pos s.val with h | h
  · exact Or.inl (Fin.ext (by simp [h]))
  · exact Or.inr (Fin.ext (by simp; omega))

lemma toMeasure_apply {S : ℕ} (d : MDPStateDistribution S) (A : Set (Fin S)) :
    d.toMeasure A = ∑ i, (d.prob i : ℝ≥0∞) * A.indicator 1 i := by
  rw [MDPStateDistribution.toMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

lemma toMeasure_real_singleton {S : ℕ} (d : MDPStateDistribution S) (s : Fin S) :
    (d.toMeasure).real {s} = (d.prob s : ℝ) := by
  rw [measureReal_def, toMeasure_apply, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- Integrating a function of the state alone against the step kernel. -/
lemma integral_step_state {S A n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (h : MDPTrajectory S A n) (g : Fin S → ℝ) :
    (∫ p, g p.1 ∂(mdpStepKernel M μ0 π n h)) = ∫ s, g s ∂(mdpStateKernel M μ0 n h) := by
  rw [mdpStepKernel, ProbabilityTheory.integral_compProd (by exact Integrable.of_finite)]
  simp

lemma integral_state_zero {S A : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A 0) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 0 h)) = ∫ s, g s ∂μ0.toMeasure := by
  rw [mdpStateKernel]; simp

lemma integral_state_succ {S A n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A (n + 1)) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 (n + 1) h))
      = ∫ s, g s ∂(M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure := by
  rw [mdpStateKernel, Kernel.comap_apply]; rfl

lemma integral_two_point (d : MDPStateDistribution 2) (g : Fin 2 → ℝ) :
    (∫ s, g s ∂d.toMeasure) = (d.prob 0 : ℝ) * g 0 + (d.prob 1 : ℝ) * g 1 := by
  rw [integral_fintype (by exact Integrable.of_finite), Fin.sum_univ_two,
    toMeasure_real_singleton, toMeasure_real_singleton, smul_eq_mul, smul_eq_mul]

variable {m : ℕ}

/-- The probability that the state of round `n + 1` is the rewarding state. -/
noncomputable def w (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (n : ℕ) : ℝ :=
  ∫ h, (∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π n h))
      ∂(mdpMeasure M (mdpStateDirac 0) π n)

lemma w_zero (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) : w M π 0 = 0 := by
  have hz : ∀ h : MDPTrajectory 2 m 0,
      (∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π 0 h)) = 0 := by
    intro h
    rw [integral_step_state, integral_state_zero, integral_two_point]
    simp [ind1s, mdpStateDirac]
  rw [w]
  simp [hz]

/-- The law of the state at the end of a trajectory of length `n + 1` is `w M π n`. -/
lemma integral_last_state (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (n : ℕ) :
    (∫ h, ind1s (h (Fin.last n)).1 ∂(mdpMeasure M (mdpStateDirac 0) π (n + 1))) = w M π n := by
  rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac 0) π n
    (fun h' => ind1s (h' (Fin.last n)).1), w]
  simp

lemma w_succ {δ : ℝ} (M : FiniteMDP 2 m) (π : MDPPolicy 2 m)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ) (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ) (n : ℕ) :
    w M π (n + 1) = δ + (1 - 2 * δ) * w M π n := by
  have hrow : ∀ (s : Fin 2) (b : Fin m),
      (∫ t, ind1s t ∂(M.transitionDist s b).toMeasure) = δ + (1 - 2 * δ) * ind1s s := by
    intro s b
    rw [integral_two_point]
    have h1 : ∀ (s' : Fin 2) (b' : Fin m), ((M.transitionDist s' b').prob 1 : ℝ) = (M.P s' b' 1 : ℝ) :=
      fun _ _ => rfl
    rcases fin2_cases s with hs | hs
    · subst hs
      rw [h1, hP0 b]
      simp [ind1s]
    · subst hs
      have hsum := M.P_sum_one 1 b
      rw [Fin.sum_univ_two] at hsum
      have : (M.P 1 b 0 : ℝ) + (M.P 1 b 1 : ℝ) = 1 := by
        rw [← NNReal.coe_add, hsum, NNReal.coe_one]
      rw [hP1 b] at this
      rw [h1]
      simp only [ind1s]
      norm_num
      linarith
  have hinner : ∀ h : MDPTrajectory 2 m (n + 1),
      (∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π (n + 1) h))
        = δ + (1 - 2 * δ) * ind1s (h (Fin.last n)).1 := by
    intro h
    rw [integral_step_state, integral_state_succ]
    exact hrow _ _
  rw [w]
  simp_rw [hinner]
  rw [integral_add (integrable_const _) (by exact Integrable.of_finite)]
  rw [integral_const, integral_const_mul, integral_last_state]
  simp

lemma w_eq {δ : ℝ} (M : FiniteMDP 2 m) (π : MDPPolicy 2 m)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ) (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ) (n : ℕ) :
    w M π n = (1 - (1 - 2 * δ) ^ n) / 2 := by
  induction n with
  | zero => rw [w_zero]; simp
  | succ n ih =>
      rw [w_succ M π hP1 hP0 n, ih]
      ring

/-- The reward accumulated over `n` rounds. -/
noncomputable def R (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (n : ℕ) : ℝ :=
  ∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac 0) π n)

lemma reward_snoc (M : FiniteMDP 2 m) (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    {n : ℕ} (h : MDPTrajectory 2 m n) (p : Fin 2 × Fin m) :
    mdpTrajectoryReward M (Fin.snoc h p) = mdpTrajectoryReward M h + ind1s p.1 := by
  rw [mdpTrajectoryReward, mdpTrajectoryReward, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro t _
    rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]
    rcases fin2_cases p.1 with hs | hs
    · rw [hs, hr0]; simp [ind1s, hs]
    · rw [hs, hr1]; simp [ind1s, hs]

lemma R_zero (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) : R M π 0 = 0 := by
  rw [R]
  have : ∀ h : MDPTrajectory 2 m 0, mdpTrajectoryReward M h = 0 := by
    intro h; rw [mdpTrajectoryReward]; simp
  simp [this]

lemma R_succ (M : FiniteMDP 2 m) (π : MDPPolicy 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1) (n : ℕ) :
    R M π (n + 1) = R M π n + w M π n := by
  rw [R, BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac 0) π n
    (fun h' => mdpTrajectoryReward M h')]
  simp_rw [reward_snoc M hr0 hr1]
  have hin : ∀ h : MDPTrajectory 2 m n,
      (∫ p, (mdpTrajectoryReward M h + ind1s p.1)
          ∂(mdpStepKernel M (mdpStateDirac 0) π n h))
        = mdpTrajectoryReward M h
            + ∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π n h) := by
    intro h
    rw [integral_add (integrable_const _) (by exact Integrable.of_finite), integral_const]
    simp
  simp_rw [hin]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite), R, w]

lemma R_eq_sum (M : FiniteMDP 2 m) (π : MDPPolicy 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1) (T : ℕ) :
    R M π T = ∑ n ∈ Finset.range T, w M π n := by
  induction T with
  | zero => rw [R_zero]; simp
  | succ T ih => rw [R_succ M π hr0 hr1 T, ih, Finset.sum_range_succ]

/-- The indicator of "the planted action was played in the reference state". -/
def inda {m : ℕ} (a : Fin m) (p : Fin 2 × Fin m) : ℝ := if p = (0, a) then 1 else 0

/-- The probability that round `n + 1` plays the planted action in state `s_0`. -/
noncomputable def q (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m) (n : ℕ) : ℝ :=
  ∫ h, (∫ p, inda a p ∂(mdpStepKernel M (mdpStateDirac 0) π n h))
      ∂(mdpMeasure M (mdpStateDirac 0) π n)

lemma q_nonneg (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m) (n : ℕ) : 0 ≤ q M π a n := by
  rw [q]
  apply integral_nonneg
  intro h
  apply integral_nonneg
  intro p
  rw [inda]
  positivity

lemma integral_last_inda (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m) (n : ℕ) :
    (∫ h, inda a (h (Fin.last n)) ∂(mdpMeasure M (mdpStateDirac 0) π (n + 1))) = q M π a n := by
  rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac 0) π n
    (fun h' => inda a (h' (Fin.last n))), q]
  simp

/-- The state recursion for the planted gadget: the escape probability carries the
extra `ε` exactly on the rounds that play the planted action in `s_0`. -/
lemma w_succ_planted {δ ε : ℝ} (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0)) (n : ℕ) :
    w M π (n + 1) = δ + (1 - 2 * δ) * w M π n + ε * q M π a n := by
  have hrow : ∀ (s : Fin 2) (b : Fin m),
      (∫ t, ind1s t ∂(M.transitionDist s b).toMeasure)
        = δ + (1 - 2 * δ) * ind1s s + ε * inda a (s, b) := by
    intro s b
    rw [integral_two_point]
    have h1 : ∀ (s' : Fin 2) (b' : Fin m),
        ((M.transitionDist s' b').prob 1 : ℝ) = (M.P s' b' 1 : ℝ) := fun _ _ => rfl
    rcases fin2_cases s with hs | hs
    · subst hs
      rw [h1, hP0 b]
      by_cases hb : b = a
      · rw [if_pos hb]
        simp [ind1s, inda, hb]
      · rw [if_neg hb]
        have hne : ((0 : Fin 2), b) ≠ ((0 : Fin 2), a) := by
          intro hcon
          exact hb (congrArg Prod.snd hcon)
        simp [ind1s, inda, hne, hb]
    · subst hs
      have hsum := M.P_sum_one 1 b
      rw [Fin.sum_univ_two] at hsum
      have hs2 : (M.P 1 b 0 : ℝ) + (M.P 1 b 1 : ℝ) = 1 := by
        rw [← NNReal.coe_add, hsum, NNReal.coe_one]
      rw [hP1 b] at hs2
      rw [h1]
      have hne : ((1 : Fin 2), b) ≠ ((0 : Fin 2), a) := by
        intro hcon
        have hone : (1 : Fin 2) = 0 := congrArg Prod.fst hcon
        exact absurd hone (by decide)
      simp only [ind1s, inda, if_neg hne]
      norm_num
      linarith
  have hinner : ∀ h : MDPTrajectory 2 m (n + 1),
      (∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π (n + 1) h))
        = δ + (1 - 2 * δ) * ind1s (h (Fin.last n)).1 + ε * inda a (h (Fin.last n)) := by
    intro h
    rw [integral_step_state, integral_state_succ]
    have := hrow (h (Fin.last n)).1 (h (Fin.last n)).2
    rw [this]
  rw [w]
  simp_rw [hinner]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite),
    integral_add (integrable_const _) (by exact Integrable.of_finite)]
  rw [integral_const, integral_const_mul, integral_const_mul, integral_last_state,
    integral_last_inda]
  simp



/-- Under the memoryless policy that always plays `a`, the planted action is played
in `s_∘` exactly when the state is `s_∘`. -/
lemma q_always (M : FiniteMDP 2 m) (a : Fin m) (n : ℕ) :
    q M (mdpMemorylessDetPolicy (fun _ => a)) a n
      = 1 - w M (mdpMemorylessDetPolicy (fun _ => a)) n := by
  have hinner : ∀ h : MDPTrajectory 2 m n,
      (∫ p, inda a p ∂(mdpStepKernel M (mdpStateDirac 0) (mdpMemorylessDetPolicy (fun _ => a)) n h))
        = 1 - ∫ p, ind1s p.1
              ∂(mdpStepKernel M (mdpStateDirac 0) (mdpMemorylessDetPolicy (fun _ => a)) n h) := by
    intro h
    rw [mdpStepKernel, ProbabilityTheory.integral_compProd (by exact Integrable.of_finite),
      ProbabilityTheory.integral_compProd (by exact Integrable.of_finite)]
    have hsel : ∀ s : Fin 2,
        (∫ b, inda a (s, b) ∂((mdpMemorylessDetPolicy (fun _ : Fin 2 => a)).select n (h, s)))
          = 1 - ind1s s := by
      intro s
      rw [mdpMemorylessDetPolicy]
      simp only [Kernel.deterministic_apply]
      rw [integral_dirac]
      rcases fin2_cases s with hs | hs
      · subst hs; simp [inda, ind1s]
      · subst hs
        have hne : ((1 : Fin 2), a) ≠ ((0 : Fin 2), a) := by
          intro hcon
          have hone : (1 : Fin 2) = 0 := congrArg Prod.fst hcon
          exact absurd hone (by decide)
        simp [inda, ind1s, hne]
    simp_rw [hsel]
    have hsel2 : ∀ s : Fin 2,
        (∫ _b, ind1s s ∂((mdpMemorylessDetPolicy (fun _ : Fin 2 => a)).select n (h, s)))
          = ind1s s := by
      intro s
      simp
    simp_rw [hsel2]
    rw [integral_sub (integrable_const _) (by exact Integrable.of_finite), integral_const]
    simp
  rw [q, w]
  simp_rw [hinner]
  rw [integral_sub (integrable_const _) (by exact Integrable.of_finite), integral_const]
  simp

/-- The state law under the always-`a` policy converges geometrically to the
stationary mass of the rewarding state. -/
lemma w_always {δ ε : ℝ} (M : FiniteMDP 2 m) (a : Fin m)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0)) (n : ℕ) :
    w M (mdpMemorylessDetPolicy (fun _ => a)) n
      = ((δ + ε) / (2 * δ + ε)) * (1 - (1 - 2 * δ - ε) ^ n) := by
  have hden : (0:ℝ) < 2 * δ + ε := by linarith
  induction n with
  | zero => rw [w_zero]; simp
  | succ n ih =>
      rw [w_succ_planted M (mdpMemorylessDetPolicy (fun _ => a)) a hP1 hP0 n, q_always, ih]
      field_simp
      ring

end JaoGain

open JaoGain

theorem solution
    {m : ℕ} (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (a : Fin m) (M : FiniteMDP 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0)) :
    (δ + ε) / (2 * δ + ε) ≤ mdpOptimalGain M := by
  set ρ : ℝ := (δ + ε) / (2 * δ + ε) with hρ
  set c : ℝ := 1 - 2 * δ - ε with hc
  have hden : (0:ℝ) < 2 * δ + ε := by linarith
  have hc0 : (0:ℝ) ≤ c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  have hρ0 : (0:ℝ) ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hden]; linarith
  set π₀ : MDPPolicy 2 m := mdpMemorylessDetPolicy (fun _ => a) with hπ₀
  haveI : Nonempty (MDPPolicy 2 m) := ⟨π₀⟩
  -- every gain is at most one
  have hrew_le : ∀ (π : MDPPolicy 2 m) (s : Fin 2) (n : ℕ),
      mdpExpectedReward M (mdpStateDirac s) π n ≤ n := by
    intro π s n
    rw [mdpExpectedReward]
    calc (∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac s) π n))
        ≤ ∫ _h, (n : ℝ) ∂(mdpMeasure M (mdpStateDirac s) π n) := by
          apply integral_mono (by exact Integrable.of_finite) (by exact Integrable.of_finite)
          intro h
          rw [mdpTrajectoryReward]
          calc (∑ t, M.r (h t).1 (h t).2) ≤ ∑ _t : Fin n, (1:ℝ) :=
                Finset.sum_le_sum (fun t _ => (M.r_mem_Icc (h t).1 (h t).2).2)
            _ = (n : ℝ) := by simp
      _ = (n : ℝ) := by simp
  have hrew_nonneg : ∀ (π : MDPPolicy 2 m) (s : Fin 2) (n : ℕ),
      0 ≤ mdpExpectedReward M (mdpStateDirac s) π n := by
    intro π s n
    rw [mdpExpectedReward]
    apply integral_nonneg
    intro h
    rw [mdpTrajectoryReward]
    exact Finset.sum_nonneg (fun t _ => (M.r_mem_Icc (h t).1 (h t).2).1)
  have hgain_le : ∀ (π : MDPPolicy 2 m) (s : Fin 2), mdpGain M π s ≤ 1 := by
    intro π s
    rw [mdpGain]
    apply Filter.limsup_le_of_le
    · refine ⟨0, ?_⟩
      intro x hx
      rw [Filter.eventually_map] at hx
      have h1 : ∀ᶠ n : ℕ in Filter.atTop,
          (0:ℝ) ≤ mdpExpectedReward M (mdpStateDirac s) π n / n := by
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
        have := hrew_nonneg π s n
        positivity
      obtain ⟨n, hn⟩ := (h1.and hx).exists
      linarith [hn.1, hn.2]
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      rw [div_le_one hn0]
      exact hrew_le π s n
  -- the gain of the always-`a` policy from `s_∘`
  have hR : ∀ n : ℕ, mdpExpectedReward M (mdpStateDirac 0) π₀ n
      = ρ * (n : ℝ) - ρ * ((1 - c ^ n) / (1 - c)) := by
    intro n
    have h1 : mdpExpectedReward M (mdpStateDirac 0) π₀ n = ∑ k ∈ Finset.range n, w M π₀ k :=
      R_eq_sum M π₀ hr0 hr1 n
    rw [h1]
    have h2 : ∀ k ∈ Finset.range n, w M π₀ k = ρ * (1 - c ^ k) := by
      intro k _
      rw [hπ₀, w_always M a hδ0 hδ hε0 hεδ hP1 hP0 k, hρ, hc]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
    have h3 : ∑ k ∈ Finset.range n, (1 - c ^ k) = (n : ℝ) - (1 - c ^ n) / (1 - c) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hne : c ≠ 1 := ne_of_lt hc1
      rw [geom_sum_eq hne]
      have h1c : (0:ℝ) < 1 - c := by linarith
      field_simp
      ring
    rw [h3]
    ring
  have htend : Filter.Tendsto
      (fun n : ℕ => mdpExpectedReward M (mdpStateDirac 0) π₀ n / n) Filter.atTop (nhds ρ) := by
    have h1c : (0:ℝ) < 1 - c := by linarith
    have hform : ∀ n : ℕ, 1 ≤ n →
        mdpExpectedReward M (mdpStateDirac 0) π₀ n / n
          = ρ - (ρ / (1 - c)) * ((1 - c ^ n) / n) := by
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      rw [hR n]
      field_simp
    have hzero : Filter.Tendsto (fun n : ℕ => (1 - c ^ n) / (n : ℝ)) Filter.atTop (nhds 0) := by
      apply squeeze_zero' (g := fun n : ℕ => 1 / (n : ℝ))
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
        have : (0:ℝ) ≤ 1 - c ^ n := by
          have : c ^ n ≤ 1 := pow_le_one₀ hc0 hc1.le
          linarith
        positivity
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
        have hcn : (0:ℝ) ≤ c ^ n := pow_nonneg hc0 n
        apply div_le_div_of_nonneg_right (by linarith) hn0.le
      · exact tendsto_one_div_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := ρ) (f := Filter.atTop (α := ℕ))).sub
      (hzero.const_mul (ρ / (1 - c)))
    simp only [mul_zero, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (hform n hn).symm
  have hgain : mdpGain M π₀ 0 = ρ := by
    rw [mdpGain]
    exact htend.limsup_eq
  -- push through the two suprema
  calc ρ = mdpGain M π₀ 0 := hgain.symm
    _ ≤ ⨆ π : MDPPolicy 2 m, mdpGain M π 0 := by
        apply le_ciSup (f := fun π : MDPPolicy 2 m => mdpGain M π 0)
        exact ⟨1, by rintro x ⟨π, rfl⟩; exact hgain_le π 0⟩
    _ ≤ mdpOptimalGain M := by
        rw [mdpOptimalGain]
        apply le_ciSup (f := fun s : Fin 2 => ⨆ π : MDPPolicy 2 m, mdpGain M π s)
        refine ⟨1, ?_⟩
        rintro x ⟨s, rfl⟩
        apply ciSup_le
        intro π
        exact hgain_le π s
