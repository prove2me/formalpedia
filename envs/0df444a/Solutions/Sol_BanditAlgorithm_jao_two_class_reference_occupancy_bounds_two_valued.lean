-- Prove2me | solution 1 for BanditAlgorithm.jao_two_class_reference_occupancy_bounds_two_valued
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T03:24:07.571376+00:00
-- url     : https://prove2.me/submissions/521df653-cbeb-4f8a-a037-ea8f851431b1

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Algebra.Field.GeomSum
import Definitions.Def_UCRL2ConfidenceSets
import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace JaoTwoClassOcc

variable {S A : ℕ}

lemma toMeasure_apply (d : MDPStateDistribution S) (B : Set (Fin S)) :
    d.toMeasure B = ∑ i, (d.prob i : ℝ≥0∞) * B.indicator 1 i := by
  rw [MDPStateDistribution.toMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

lemma toMeasure_real_singleton (d : MDPStateDistribution S) (s : Fin S) :
    (d.toMeasure).real {s} = (d.prob s : ℝ) := by
  rw [measureReal_def, toMeasure_apply, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ s) h

lemma integral_fin (d : MDPStateDistribution S) (g : Fin S → ℝ) :
    (∫ t, g t ∂d.toMeasure) = ∑ t, (d.prob t : ℝ) * g t := by
  rw [integral_fintype (by exact Integrable.of_finite)]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [toMeasure_real_singleton, smul_eq_mul]

/-- A distribution whose mass at two distinct points already sums to one is
supported on those two points. -/
lemma integral_two_point (d : MDPStateDistribution S) (u v : Fin S) (huv : u ≠ v)
    (hsum : (d.prob u : ℝ) + (d.prob v : ℝ) = 1) (g : Fin S → ℝ) :
    (∫ t, g t ∂d.toMeasure) = (d.prob u : ℝ) * g u + (d.prob v : ℝ) * g v := by
  classical
  have htot : ∑ t, (d.prob t : ℝ) = 1 := by
    have := d.sum_one
    have : ((∑ t, d.prob t : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by rw [this]
    simpa using this
  set P : Finset (Fin S) := {u, v} with hP
  have hpair : ∑ t ∈ P, (d.prob t : ℝ) = 1 := by
    rw [hP, Finset.sum_pair huv, hsum]
  have hrest : ∑ t ∈ Finset.univ \ P, (d.prob t : ℝ) = 0 := by
    have hsplit := Finset.sum_sdiff (f := fun t => (d.prob t : ℝ)) (Finset.subset_univ P)
    rw [hpair, htot] at hsplit
    linarith
  have hzero : ∀ t ∈ Finset.univ \ P, (d.prob t : ℝ) = 0 := by
    intro t ht
    by_contra hne
    have hpos : 0 < (d.prob t : ℝ) := lt_of_le_of_ne (d.prob t).coe_nonneg (Ne.symm hne)
    have : 0 < ∑ x ∈ Finset.univ \ P, (d.prob x : ℝ) :=
      Finset.sum_pos' (fun x _ => (d.prob x).coe_nonneg) ⟨t, ht, hpos⟩
    linarith [hrest]
  rw [integral_fin, ← Finset.sum_sdiff (Finset.subset_univ P)]
  rw [Finset.sum_eq_zero (fun t ht => by rw [hzero t ht]; ring)]
  rw [hP, Finset.sum_pair huv]
  ring

lemma integral_step_state {n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (h : MDPTrajectory S A n) (g : Fin S → ℝ) :
    (∫ p, g p.1 ∂(mdpStepKernel M μ0 π n h)) = ∫ s, g s ∂(mdpStateKernel M μ0 n h) := by
  rw [mdpStepKernel, ProbabilityTheory.integral_compProd (by exact Integrable.of_finite)]
  simp

lemma integral_state_zero (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A 0) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 0 h)) = ∫ s, g s ∂μ0.toMeasure := by
  rw [mdpStateKernel]; simp

lemma integral_state_succ {n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A (n + 1)) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 (n + 1) h))
      = ∫ s, g s ∂(M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure := by
  rw [mdpStateKernel, Kernel.comap_apply]; rfl

/-- The probability that the state of round `n + 1` has class one. -/
noncomputable def w (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A)
    (s₀ : Fin S) (n : ℕ) : ℝ :=
  ∫ h, (∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π n h))
      ∂(mdpMeasure M (mdpStateDirac s₀) π n)

lemma w_zero (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S) :
    w ρ M π s₀ 0 = ρ s₀ := by
  have hz : ∀ h : MDPTrajectory S A 0,
      (∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π 0 h)) = ρ s₀ := by
    intro h
    rw [integral_step_state, integral_state_zero, integral_fin]
    rw [Finset.sum_eq_single s₀]
    · simp [mdpStateDirac]
    · intro b _ hb
      simp [mdpStateDirac, hb]
    · intro hcon
      exact absurd (Finset.mem_univ s₀) hcon
  rw [w]
  simp [hz]

lemma integral_last_state (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A)
    (s₀ : Fin S) (n : ℕ) :
    (∫ h, ρ (h (Fin.last n)).1 ∂(mdpMeasure M (mdpStateDirac s₀) π (n + 1)))
      = w ρ M π s₀ n := by
  rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac s₀) π n
    (fun h' => ρ (h' (Fin.last n)).1), w]
  simp

/-- The one-step recursion, given the pointwise row identity. -/
lemma w_succ {δ : ℝ} (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A)
    (s₀ : Fin S)
    (hrow : ∀ (s : Fin S) (b : Fin A),
      (∫ t, ρ t ∂(M.transitionDist s b).toMeasure) = δ + (1 - 2 * δ) * ρ s) (n : ℕ) :
    w ρ M π s₀ (n + 1) = δ + (1 - 2 * δ) * w ρ M π s₀ n := by
  have hinner : ∀ h : MDPTrajectory S A (n + 1),
      (∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π (n + 1) h))
        = δ + (1 - 2 * δ) * ρ (h (Fin.last n)).1 := by
    intro h
    rw [integral_step_state, integral_state_succ]
    exact hrow _ _
  rw [w]
  simp_rw [hinner]
  rw [integral_add (integrable_const _) (by exact Integrable.of_finite)]
  rw [integral_const, integral_const_mul, integral_last_state]
  simp

lemma w_eq {δ : ℝ} (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S)
    (hrow : ∀ (s : Fin S) (b : Fin A),
      (∫ t, ρ t ∂(M.transitionDist s b).toMeasure) = δ + (1 - 2 * δ) * ρ s) (n : ℕ) :
    w ρ M π s₀ n = 1 / 2 + (ρ s₀ - 1 / 2) * (1 - 2 * δ) ^ n := by
  induction n with
  | zero => rw [w_zero]; simp
  | succ n ih =>
      rw [w_succ ρ M π s₀ hrow n, ih]
      ring

/-- The reward accumulated over `n` rounds. -/
noncomputable def R (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S) (n : ℕ) : ℝ :=
  ∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac s₀) π n)

lemma reward_snoc (ρ : Fin S → ℝ) (M : FiniteMDP S A) (hr : ∀ s b, M.r s b = ρ s)
    {n : ℕ} (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    mdpTrajectoryReward M (Fin.snoc h p) = mdpTrajectoryReward M h + ρ p.1 := by
  rw [mdpTrajectoryReward, mdpTrajectoryReward, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro t _
    rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last, hr]

lemma R_zero (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S) : R M π s₀ 0 = 0 := by
  rw [R]
  have : ∀ h : MDPTrajectory S A 0, mdpTrajectoryReward M h = 0 := by
    intro h; rw [mdpTrajectoryReward]; simp
  simp [this]

lemma R_succ (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S)
    (hr : ∀ s b, M.r s b = ρ s) (n : ℕ) :
    R M π s₀ (n + 1) = R M π s₀ n + w ρ M π s₀ n := by
  rw [R, BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac s₀) π n
    (fun h' => mdpTrajectoryReward M h')]
  simp_rw [reward_snoc ρ M hr]
  have hin : ∀ h : MDPTrajectory S A n,
      (∫ p, (mdpTrajectoryReward M h + ρ p.1)
          ∂(mdpStepKernel M (mdpStateDirac s₀) π n h))
        = mdpTrajectoryReward M h
            + ∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π n h) := by
    intro h
    rw [integral_add (integrable_const _) (by exact Integrable.of_finite), integral_const]
    simp
  simp_rw [hin]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite), R, w]

lemma R_eq_sum (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S)
    (hr : ∀ s b, M.r s b = ρ s) (T : ℕ) :
    R M π s₀ T = ∑ n ∈ Finset.range T, w ρ M π s₀ n := by
  induction T with
  | zero => rw [R_zero]; simp
  | succ T ih => rw [R_succ ρ M π s₀ hr T, ih, Finset.sum_range_succ]

/-- Pointwise: the plays of the plantable pairs, plus the reward, is at most `T`. -/
lemma count_le {m : ℕ} (ρ : Fin S → ℝ) (M : FiniteMDP S A) (hr : ∀ s b, M.r s b = ρ s)
    (hρ01 : ∀ s, ρ s = 0 ∨ ρ s = 1)
    (arm : Fin m → Fin S × Fin A) (hinj : Function.Injective arm)
    (harm0 : ∀ i, ρ (arm i).1 = 0)
    {T : ℕ} (h : MDPTrajectory S A T) :
    mdpTrajectoryReward M h
        + ∑ i : Fin m, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ) ≤ T := by
  classical
  have hrew : mdpTrajectoryReward M h = ∑ t : Fin T, ρ (h t).1 := by
    rw [mdpTrajectoryReward]
    exact Finset.sum_congr rfl fun t _ => hr _ _
  have hcount : (∑ i : Fin m, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ))
      = ∑ t : Fin T, ∑ i : Fin m, (if h t = arm i then (1 : ℝ) else 0) := by
    simp only [mdpVisitCount]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro t _
    have hi : (t : ℕ) < T := t.isLt
    by_cases hz : h t = ((arm i).1, (arm i).2)
    · rw [if_pos ⟨hi, hz⟩, if_pos (by simpa using hz)]
    · rw [if_neg (fun hc => hz hc.2), if_neg (by simpa using hz)]
  have hterm : ∀ t : Fin T,
      ρ (h t).1 + (∑ i : Fin m, (if h t = arm i then (1 : ℝ) else 0)) ≤ 1 := by
    intro t
    by_cases hex : ∃ i, h t = arm i
    · obtain ⟨i, hi⟩ := hex
      have hsum : (∑ j : Fin m, (if h t = arm j then (1 : ℝ) else 0)) = 1 := by
        rw [Finset.sum_eq_single i]
        · rw [if_pos hi]
        · intro j _ hj
          refine if_neg ?_
          intro hc
          exact hj (hinj (hi ▸ hc)).symm
        · intro hcon
          exact absurd (Finset.mem_univ i) hcon
      have : ρ (h t).1 = 0 := by rw [hi]; exact harm0 i
      rw [hsum, this]; norm_num
    · push_neg at hex
      have hsum : (∑ j : Fin m, (if h t = arm j then (1 : ℝ) else 0)) = 0 :=
        Finset.sum_eq_zero fun j _ => if_neg (hex j)
      rcases hρ01 (h t).1 with h0 | h1
      · rw [hsum, h0]; norm_num
      · rw [hsum, h1]; norm_num
  rw [hrew, hcount, ← Finset.sum_add_distrib]
  calc ∑ t : Fin T, (ρ (h t).1 + ∑ i : Fin m, (if h t = arm i then (1 : ℝ) else 0))
      ≤ ∑ _t : Fin T, (1 : ℝ) := Finset.sum_le_sum fun t _ => hterm t
    _ = T := by simp

end JaoTwoClassOcc

open JaoTwoClassOcc

theorem solution {S A m : ℕ}
    (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3)
    (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
    (hρ01 : ∀ s, ρ s = 0 ∨ ρ s = 1)
    (arm : Fin m → Fin S × Fin A) (harm : Function.Injective arm)
    (harm0 : ∀ i, ρ (arm i).1 = 0) (M₀ : FiniteMDP S A)
    (hrM₀ : ∀ s b, M₀.r s b = ρ s)
    (hrow0M₀ : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M₀.P s b (up s) : ℝ) = δ ∧
        (M₀.P s b (nav s b) : ℝ) = 1 - δ)
    (hrow1M₀ : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M₀.P s b (down s) : ℝ) = δ ∧ (M₀.P s b s : ℝ) = 1 - δ)
    (T : ℕ) (π : MDPPolicy S A) (s₀ : Fin S) :
    (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
        ≤ (T : ℝ) / 2 + 1 / (2 * δ)
      ∧ ∑ i : Fin m,
            (∫ h, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ)
              ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
          ≤ (T : ℝ) / 2 + 1 / (2 * δ) := by
  classical
  -- the reference row identity: `∫ ρ = δ + (1 - 2δ)·ρ s`, valid at every state
  have hrow : ∀ (s : Fin S) (b : Fin A),
      (∫ t, ρ t ∂(M₀.transitionDist s b).toMeasure) = δ + (1 - 2 * δ) * ρ s := by
    intro s b
    have hp : ∀ (s' : Fin S) (b' : Fin A) (t : Fin S),
        (((M₀.transitionDist s' b').prob t : ℝ)) = ((M₀.P s' b' t : ℝ)) := fun _ _ _ => rfl
    rcases hρ01 s with hs | hs
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hrow0M₀ s b hs
      rw [integral_two_point _ (up s) (nav s b) h3 (by rw [hp, hp, h4, h5]; ring)]
      rw [hp, hp, h4, h5, h1, h2, hs]; ring
    · obtain ⟨h1, h2, h3, h4⟩ := hrow1M₀ s b hs
      rw [integral_two_point _ (down s) s h2 (by rw [hp, hp, h3, h4]; ring)]
      rw [hp, hp, h3, h4, h1, hs]; ring
  -- the reward is the partial sum of the class-one probabilities
  have hrew : (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
      = ∑ n ∈ Finset.range T, (1 / 2 + (ρ s₀ - 1 / 2) * (1 - 2 * δ) ^ n) := by
    have := R_eq_sum ρ M₀ π s₀ hrM₀ T
    rw [R] at this
    rw [this]
    exact Finset.sum_congr rfl fun n _ => w_eq ρ M₀ π s₀ hrow n
  -- the geometric remainder
  have hr0 : (0 : ℝ) ≤ 1 - 2 * δ := by linarith
  have hr1 : (1 - 2 * δ) < 1 := by linarith
  have hgeom : ∑ n ∈ Finset.range T, (1 - 2 * δ) ^ n = (1 - (1 - 2 * δ) ^ T) / (2 * δ) := by
    rw [geom_sum_eq (by linarith)]
    field_simp
    ring
  have hpow0 : (0 : ℝ) ≤ (1 - 2 * δ) ^ T := pow_nonneg hr0 T
  have hpow1 : (1 - 2 * δ) ^ T ≤ 1 := pow_le_one₀ hr0 (le_of_lt hr1)
  have hgeom0 : (0 : ℝ) ≤ ∑ n ∈ Finset.range T, (1 - 2 * δ) ^ n := by
    rw [hgeom]; positivity
  have hgeomle : (∑ n ∈ Finset.range T, (1 - 2 * δ) ^ n) ≤ 1 / (2 * δ) := by
    rw [hgeom, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsum : (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
      = (T : ℝ) / 2 + (ρ s₀ - 1 / 2) * ∑ n ∈ Finset.range T, (1 - 2 * δ) ^ n := by
    rw [hrew, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_range]
    ring
  -- `|ρ s₀ - 1/2| ≤ 1/2`
  have hc : -(1 / 2 : ℝ) ≤ ρ s₀ - 1 / 2 ∧ ρ s₀ - 1 / 2 ≤ 1 / 2 := by
    rcases hρ01 s₀ with h | h <;> rw [h] <;> norm_num
  have hδ4 : (0 : ℝ) < 1 / (2 * δ) := by positivity
  have hupper : (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
      ≤ (T : ℝ) / 2 + 1 / 2 * (1 / (2 * δ)) := by
    rw [hsum]
    have := mul_le_mul_of_nonneg_right hc.2 hgeom0
    nlinarith [hc.2, hgeom0, hgeomle]
  have hlower : (T : ℝ) / 2 - 1 / 2 * (1 / (2 * δ))
      ≤ ∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T) := by
    rw [hsum]
    nlinarith [hc.1, hgeom0, hgeomle]
  refine ⟨by nlinarith [hupper], ?_⟩
  -- the plantable pairs are disjoint and class zero, so their plays fit in the
  -- complement of the reward
  have hswap : ∑ i : Fin m,
        (∫ h, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ)
          ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
      = ∫ h, (∑ i : Fin m, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ))
          ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T) := by
    rw [integral_finsetSum]
    intro i _
    exact Integrable.of_finite
  have hpt : ∀ h : MDPTrajectory S A T,
      (∑ i : Fin m, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ))
        ≤ (T : ℝ) - mdpTrajectoryReward M₀ h := by
    intro h
    linarith [count_le ρ M₀ hrM₀ hρ01 arm harm harm0 h]
  have hint : (∫ h, (∑ i : Fin m, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ))
          ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
      ≤ (T : ℝ) - ∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T) := by
    have hle := integral_mono (μ := mdpMeasure M₀ (mdpStateDirac s₀) π T)
      (f := fun h => ∑ i : Fin m, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ))
      (g := fun h => (T : ℝ) - mdpTrajectoryReward M₀ h)
      Integrable.of_finite Integrable.of_finite hpt
    rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const] at hle
    simpa using hle
  rw [hswap]
  nlinarith [hint, hlower]
