-- Prove2me | solution 1 for BanditAlgorithm.exp4_mixture_estimate_expectation_eq_reward
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T00:24:14.662309+00:00
-- url     : https://prove2.me/submissions/3d817d08-9187-4edd-a751-c367d440e14f

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Analysis

/-!
Direct proof of the conditional-expectation identity used between
Lattimore--Szepesvári, *Bandit Algorithms*, Eqs. (18.10) and (18.11),
printed p. 230.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private lemma exp4Weights_pos_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (h : BanditHistory k r)
    (m : Fin M) :
    0 < exp4ExpertWeights η 0 E r h m := by
  unfold exp4ExpertWeights expWeights
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨m, Finset.mem_univ _, Real.exp_pos _⟩

private lemma sum_exp4Weights_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (h : BanditHistory k r)
    (m₀ : Fin M) :
    ∑ m, exp4ExpertWeights η 0 E r h m = 1 := by
  unfold exp4ExpertWeights
  rw [show
      (∑ m, expWeights
          (fun j ↦ η * exp4Estimate η 0 E r h j) m) =
        (∑ m, Real.exp (η * exp4Estimate η 0 E r h m)) /
          (∑ m, Real.exp (η * exp4Estimate η 0 E r h m)) by
      simp only [expWeights, Finset.sum_div]]
  exact div_self (ne_of_gt (Finset.sum_pos'
    (fun m _ ↦ (Real.exp_pos _).le)
    ⟨m₀, Finset.mem_univ _, Real.exp_pos _⟩))

private lemma exp4Prob_nonneg_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (r : ℕ) (h : BanditHistory k r) (a : Fin k) :
    0 ≤ exp4Prob η 0 E r h a := by
  unfold exp4Prob
  exact Finset.sum_nonneg fun m _ ↦
    mul_nonneg (exp4Weights_pos_mix η E r h m).le (hE0 r m a)

private lemma sum_exp4Prob_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (r : ℕ) (h : BanditHistory k r) (m₀ : Fin M) :
    ∑ a, exp4Prob η 0 E r h a = 1 := by
  calc
    (∑ a, exp4Prob η 0 E r h a) =
        ∑ m, exp4ExpertWeights η 0 E r h m * ∑ a, E r m a := by
      simp only [exp4Prob]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ = ∑ m, exp4ExpertWeights η 0 E r h m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hE1 r m, mul_one]
    _ = 1 := sum_exp4Weights_mix η E r h m₀

private lemma exp4Estimate_measurable_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) :
    ∀ (r : ℕ) (m : Fin M),
      Measurable (fun h : BanditHistory k r ↦ exp4Estimate η 0 E r h m) := by
  intro r
  induction r with
  | zero =>
      intro m
      simp [exp4Estimate]
  | succ r ih =>
      intro m
      have hinit : Measurable
          (fun h : BanditHistory k (r + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hold : Measurable
          (fun h : BanditHistory k (r + 1) ↦
            exp4Estimate η 0 E r (Fin.init h) m) :=
        (ih m).comp hinit
      have hprob : ∀ a : Fin k, Measurable
          (fun h : BanditHistory k (r + 1) ↦
            exp4Prob η 0 E r (Fin.init h) a) := by
        intro a
        unfold exp4Prob exp4ExpertWeights expWeights
        apply Finset.measurable_sum
        intro j hj
        apply Measurable.mul
        · apply Measurable.div
          · exact Real.continuous_exp.measurable.comp
              (measurable_const.mul ((ih j).comp hinit))
          · apply Finset.measurable_sum
            intro q hq
            exact Real.continuous_exp.measurable.comp
              (measurable_const.mul ((ih q).comp hinit))
        · exact measurable_const
      have hlast : Measurable
          (fun h : BanditHistory k (r + 1) ↦ h (Fin.last r)) :=
        measurable_pi_apply (Fin.last r)
      have hinc : Measurable
          (fun h : BanditHistory k (r + 1) ↦
            ∑ a, E r m a *
              (1 - if (h (Fin.last r)).1 = a then
                (1 - (h (Fin.last r)).2) /
                  exp4Prob η 0 E r (Fin.init h) a
              else 0)) := by
        apply Finset.measurable_sum
        intro a ha
        apply Measurable.mul measurable_const
        apply Measurable.sub measurable_const
        have hcond : MeasurableSet
            {h : BanditHistory k (r + 1) | (h (Fin.last r)).1 = a} := by
          exact
            (measurableSet_singleton a).preimage (measurable_fst.comp hlast)
        have hfrac : Measurable
            (fun h : BanditHistory k (r + 1) ↦
              (1 - (h (Fin.last r)).2) /
                exp4Prob η 0 E r (Fin.init h) a) :=
          (measurable_const.sub (measurable_snd.comp hlast)).div (hprob a)
        exact Measurable.ite hcond hfrac measurable_const
      simpa only [exp4Estimate, exp4Prob, exp4ExpertWeights, add_zero, Pi.add_def, Function.comp_def] using
        hold.add hinc

private lemma exp4Prob_measurable_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (a : Fin k) :
    Measurable (fun h : BanditHistory k r ↦ exp4Prob η 0 E r h a) := by
  unfold exp4Prob exp4ExpertWeights expWeights
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.mul
  · apply Measurable.div
    · exact Real.continuous_exp.measurable.comp
        (measurable_const.mul (exp4Estimate_measurable_mix η E r m))
    · apply Finset.measurable_sum
      intro j hj
      exact Real.continuous_exp.measurable.comp
        (measurable_const.mul (exp4Estimate_measurable_mix η E r j))
  · exact measurable_const

private lemma exp4RewardIncrement_measurable_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (m : Fin M) :
    Measurable (exp4RewardIncrement η E r h m) := by
  classical
  unfold exp4RewardIncrement
  apply Finset.measurable_sum
  intro a ha
  apply Measurable.mul measurable_const
  apply Measurable.sub measurable_const
  have hset : MeasurableSet {z : Fin k × ℝ | z.1 = a} := by
    exact
      (measurableSet_singleton a).preimage measurable_fst
  have hthen : Measurable (fun z : Fin k × ℝ ↦
      (1 - z.2) / exp4Prob η 0 E r h a) :=
    (measurable_const.sub measurable_snd).div_const _
  exact Measurable.ite hset hthen measurable_const

private lemma exp4RewardIncrement_joint_measurable_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (m : Fin M) :
    Measurable (fun p : BanditHistory k r × (Fin k × ℝ) ↦
      exp4RewardIncrement η E r p.1 m p.2) := by
  classical
  unfold exp4RewardIncrement
  apply Finset.measurable_sum
  intro a ha
  apply Measurable.mul measurable_const
  apply Measurable.sub measurable_const
  have hcond : MeasurableSet
      {p : BanditHistory k r × (Fin k × ℝ) | p.2.1 = a} := by
    exact
      (measurableSet_singleton a).preimage
        (measurable_fst.comp measurable_snd)
  have hfrac : Measurable
      (fun p : BanditHistory k r × (Fin k × ℝ) ↦
        (1 - p.2.2) / exp4Prob η 0 E r p.1 a) :=
    (measurable_const.sub (measurable_snd.comp measurable_snd)).div
      ((exp4Prob_measurable_mix η E r a).comp measurable_fst)
  exact Measurable.ite hcond hfrac measurable_const

private noncomputable def exp4MixtureStep {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (z : Fin k × ℝ) : ℝ :=
  ∑ m, exp4ExpertWeights η 0 E r h m *
    exp4RewardIncrement η E r h m z

private lemma exp4MixtureStep_measurable {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (h : BanditHistory k r) :
    Measurable (exp4MixtureStep η E r h) := by
  unfold exp4MixtureStep
  exact Finset.measurable_sum _ fun m _ ↦
    measurable_const.mul (exp4RewardIncrement_measurable_mix η E r h m)

private lemma exp4MixtureStep_joint_measurable {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) :
    Measurable (fun p : BanditHistory k r × (Fin k × ℝ) ↦
      exp4MixtureStep η E r p.1 p.2) := by
  unfold exp4MixtureStep
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.mul
  · unfold exp4ExpertWeights expWeights
    apply Measurable.div
    · exact Real.continuous_exp.measurable.comp
        (measurable_const.mul
          ((exp4Estimate_measurable_mix η E r m).comp measurable_fst))
    · apply Finset.measurable_sum
      intro j hj
      exact Real.continuous_exp.measurable.comp
        (measurable_const.mul
          ((exp4Estimate_measurable_mix η E r j).comp measurable_fst))
  · exact exp4RewardIncrement_joint_measurable_mix η E r m

private lemma exp4RewardIncrement_action_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (r : ℕ) (h : BanditHistory k r) (m : Fin M)
    (a : Fin k) (y : ℝ) :
    exp4RewardIncrement η E r h m (a, y) =
      1 - E r m a * ((1 - y) / exp4Prob η 0 E r h a) := by
  classical
  unfold exp4RewardIncrement
  calc
    (∑ b, E r m b *
        (1 - if a = b then
          (1 - y) / exp4Prob η 0 E r h b
        else 0)) =
        ∑ b, (E r m b -
          if b = a then
            E r m a * ((1 - y) / exp4Prob η 0 E r h a)
          else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hba : b = a
      · subst b
        simp
        ring
      · have hab : ¬a = b := fun h ↦ hba h.symm
        simp [hba, hab]
    _ = (∑ b, E r m b) -
          ∑ b, if b = a then
            E r m a * ((1 - y) / exp4Prob η 0 E r h a)
          else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - E r m a * ((1 - y) / exp4Prob η 0 E r h a) := by
      rw [hE1 r m]
      simp

private lemma exp4MixtureStep_action_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (r : ℕ) (h : BanditHistory k r) (m₀ : Fin M)
    (a : Fin k) (y : ℝ) (hp : 0 < exp4Prob η 0 E r h a) :
    exp4MixtureStep η E r h (a, y) = y := by
  classical
  unfold exp4MixtureStep
  simp_rw [exp4RewardIncrement_action_mix η E hE1 r h]
  have hweights : ∑ m, exp4ExpertWeights η 0 E r h m = 1 :=
    sum_exp4Weights_mix η E r h m₀
  have hdecomp :
      (∑ m, exp4ExpertWeights η 0 E r h m *
        (1 - E r m a * ((1 - y) / exp4Prob η 0 E r h a))) =
        (∑ m, exp4ExpertWeights η 0 E r h m) -
          (∑ m, exp4ExpertWeights η 0 E r h m * E r m a) *
            ((1 - y) / exp4Prob η 0 E r h a) := by
    calc
      _ = ∑ m, (exp4ExpertWeights η 0 E r h m -
          (exp4ExpertWeights η 0 E r h m * E r m a) *
            ((1 - y) / exp4Prob η 0 E r h a)) := by
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = (∑ m, exp4ExpertWeights η 0 E r h m) -
          ∑ m, (exp4ExpertWeights η 0 E r h m * E r m a) *
            ((1 - y) / exp4Prob η 0 E r h a) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ m, exp4ExpertWeights η 0 E r h m) -
          (∑ m, exp4ExpertWeights η 0 E r h m * E r m a) *
            ((1 - y) / exp4Prob η 0 E r h a) := by
        rw [Finset.sum_mul]
  rw [hdecomp, hweights]
  change 1 - exp4Prob η 0 E r h a *
      ((1 - y) / exp4Prob η 0 E r h a) = y
  field_simp [ne_of_gt hp]
  ring

private lemma exp4MixtureStep_integrable_step {k M : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (r : ℕ) (h : BanditHistory k r) :
    Integrable (exp4MixtureStep η E r h)
      (adversarialStepKernel x π r h) := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  apply (integrable_map_measure
    (exp4MixtureStep_measurable η E r h).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  exact Integrable.of_finite

private lemma exp4MixtureStep_integral {k M : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (h : BanditHistory k r) (m₀ : Fin M) :
    ∫ z, exp4MixtureStep η E r h z ∂(adversarialStepKernel x π r h) =
      ∑ a, exp4Prob η 0 E r h a * x r a := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp4MixtureStep_measurable η E r h).aestronglyMeasurable]
  rw [hπ r h, integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ a : Fin k,
        (ENNReal.ofReal (exp4Prob η 0 E r h a)).toReal =
          exp4Prob η 0 E r h a :=
      fun a ↦ ENNReal.toReal_ofReal
        (exp4Prob_nonneg_mix η E hE0 r h a)
    simp_rw [htoReal]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hp0 : exp4Prob η 0 E r h a = 0
    · simp [hp0]
    · have hp : 0 < exp4Prob η 0 E r h a :=
        lt_of_le_of_ne (exp4Prob_nonneg_mix η E hE0 r h a)
          (Ne.symm hp0)
      rw [exp4MixtureStep_action_mix η E hE1 r h m₀ a (x r a) hp]
  · intro a ha
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp4MixtureStep_norm_integral_le_one {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (h : BanditHistory k r) (m₀ : Fin M) :
    (∫ z, ‖exp4MixtureStep η E r h z‖
      ∂(adversarialStepKernel x π r h)) ≤ 1 := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp4MixtureStep_measurable η E r h).norm.aestronglyMeasurable]
  rw [hπ r h, integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ a : Fin k,
        (ENNReal.ofReal (exp4Prob η 0 E r h a)).toReal =
          exp4Prob η 0 E r h a :=
      fun a ↦ ENNReal.toReal_ofReal
        (exp4Prob_nonneg_mix η E hE0 r h a)
    simp_rw [htoReal]
    have hsum : ∑ a, exp4Prob η 0 E r h a = 1 :=
      sum_exp4Prob_mix η E hE1 r h m₀
    calc
      (∑ a, exp4Prob η 0 E r h a *
          ‖exp4MixtureStep η E r h (a, x r a)‖) ≤
          ∑ a, exp4Prob η 0 E r h a := by
        apply Finset.sum_le_sum
        intro a ha
        have hp0 : 0 ≤ exp4Prob η 0 E r h a :=
          exp4Prob_nonneg_mix η E hE0 r h a
        by_cases hpzero : exp4Prob η 0 E r h a = 0
        · simp [hpzero]
        · have hp : 0 < exp4Prob η 0 E r h a :=
            lt_of_le_of_ne hp0 (Ne.symm hpzero)
          rw [exp4MixtureStep_action_mix η E hE1 r h m₀ a (x r a) hp,
            Real.norm_eq_abs, abs_of_nonneg (hx r a).1]
          exact mul_le_of_le_one_right hp0 (hx r a).2
      _ = 1 := hsum
  · intro a ha
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp4MixtureStep_integrable_joint {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (m₀ : Fin M) :
    Integrable
      (fun p : BanditHistory k r × (Fin k × ℝ) ↦
        exp4MixtureStep η E r p.1 p.2)
      ((adversarialMeasure x π r).compProd
        (adversarialStepKernel x π r)) := by
  apply (Measure.integrable_compProd_iff
    (exp4MixtureStep_joint_measurable η E r).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      exp4MixtureStep_integrable_step x π η E r h
  · apply Integrable.of_mem_Icc 0 1
    · exact (exp4MixtureStep_joint_measurable η E r).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun z ↦ norm_nonneg _)
        · exact exp4MixtureStep_norm_integral_le_one
            x hx π η E hE0 hE1 hπ r h m₀

private lemma exp4MixtureEstimate_measurable_mix {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) :
    ∀ r : ℕ,
      Measurable (fun h : BanditHistory k r ↦
        exp4MixtureEstimate η E r h) := by
  intro r
  induction r with
  | zero =>
      simp [exp4MixtureEstimate]
  | succ r ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (r + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (r + 1) ↦ h (Fin.last r)) :=
        measurable_pi_apply (Fin.last r)
      have hpair : Measurable
          (fun h : BanditHistory k (r + 1) ↦
            (Fin.init h, h (Fin.last r))) :=
        hinit.prodMk hlast
      simpa only [exp4MixtureEstimate, exp4MixtureStep, Pi.add_def, Function.comp_def] using
        (ih.comp hinit).add
          ((exp4MixtureStep_joint_measurable η E r).comp hpair)

private lemma rewardSum_measurable_mix {k r : ℕ} :
    Measurable (fun h : BanditHistory k r ↦ ∑ t, (h t).2) := by
  exact Finset.measurable_sum _ fun t _ ↦
    measurable_snd.comp (measurable_pi_apply t)

private lemma rewardStep_integrable_mix {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k)
    (r : ℕ) (h : BanditHistory k r) :
    Integrable (fun z : Fin k × ℝ ↦ z.2)
      (adversarialStepKernel x π r h) := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  apply (integrable_map_measure
    measurable_snd.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  exact Integrable.of_finite

private lemma rewardStep_integral_mix {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k)
    (η : ℝ) {M : ℕ} (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (h : BanditHistory k r) :
    (∫ z : Fin k × ℝ, z.2 ∂(adversarialStepKernel x π r h)) =
      ∑ a, exp4Prob η 0 E r h a * x r a := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      measurable_snd.aestronglyMeasurable]
  rw [hπ r h, integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ a : Fin k,
        (ENNReal.ofReal (exp4Prob η 0 E r h a)).toReal =
          exp4Prob η 0 E r h a :=
      fun a ↦ ENNReal.toReal_ofReal
        (exp4Prob_nonneg_mix η E hE0 r h a)
    simp_rw [htoReal]
  · intro a ha
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma rewardStep_norm_integral_le_one_mix {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (r : ℕ) (h : BanditHistory k r) :
    (∫ z : Fin k × ℝ, ‖z.2‖ ∂(adversarialStepKernel x π r h)) ≤ 1 := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      measurable_snd.norm.aestronglyMeasurable]
  calc
    (∫ a, ‖x r a‖ ∂(π.select r h)) ≤
        ∫ _a : Fin k, (1 : ℝ) ∂(π.select r h) := by
      apply integral_mono_ae Integrable.of_finite (integrable_const _)
      exact Filter.Eventually.of_forall fun a ↦ by
        change ‖x r a‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (hx r a).1]
        exact (hx r a).2
    _ = 1 := by simp

private lemma rewardStep_integrable_joint_mix {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (r : ℕ) :
    Integrable
      (fun p : BanditHistory k r × (Fin k × ℝ) ↦ p.2.2)
      ((adversarialMeasure x π r).compProd
        (adversarialStepKernel x π r)) := by
  apply (Measure.integrable_compProd_iff
    (measurable_snd.comp measurable_snd).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      rewardStep_integrable_mix x π r h
  · apply Integrable.of_mem_Icc 0 1
    · exact (measurable_snd.comp measurable_snd).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun z ↦ norm_nonneg _)
        · exact rewardStep_norm_integral_le_one_mix x hx π r h

private theorem exp4MixtureEstimate_integrable_integral_mix {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π) (m₀ : Fin M) :
    ∀ r : ℕ,
      Integrable (fun h : BanditHistory k r ↦
        exp4MixtureEstimate η E r h) (adversarialMeasure x π r) ∧
      Integrable (fun h : BanditHistory k r ↦
        ∑ t, (h t).2) (adversarialMeasure x π r) ∧
      (∫ h, exp4MixtureEstimate η E r h
          ∂(adversarialMeasure x π r)) =
        ∫ h, (∑ t, (h t).2) ∂(adversarialMeasure x π r) := by
  intro r
  induction r with
  | zero =>
      simp [exp4MixtureEstimate, adversarialMeasure]
  | succ r ih =>
      let μ := adversarialMeasure x π r
      let κ := adversarialStepKernel x π r
      let snoc : BanditHistory k r × (Fin k × ℝ) →
          BanditHistory k (r + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      have hsnoc : Measurable snoc := measurable_banditHistorySnoc
      have hmix_rewrite :
          (fun p ↦ exp4MixtureEstimate η E (r + 1) (snoc p)) =
            fun p ↦ exp4MixtureEstimate η E r p.1 +
              exp4MixtureStep η E r p.1 p.2 := by
        funext p
        simp [snoc, exp4MixtureEstimate, exp4MixtureStep]
      have hreward_rewrite :
          (fun p ↦ ∑ t, ((snoc p) t).2) =
            fun p ↦ (∑ t, (p.1 t).2) + p.2.2 := by
        funext p
        rw [Fin.sum_univ_castSucc]
        simp [snoc]
      have hold_mix : Integrable
          (fun p : BanditHistory k r × (Fin k × ℝ) ↦
            exp4MixtureEstimate η E r p.1)
          (μ.compProd κ) := by
        have hi : Integrable
            (fun h : BanditHistory k r ↦ exp4MixtureEstimate η E r h)
            (Measure.map Prod.fst (μ.compProd κ)) := by
          change Integrable
            (fun h : BanditHistory k r ↦ exp4MixtureEstimate η E r h)
            ((μ.compProd κ).fst)
          rw [Measure.fst_compProd]
          exact ih.1
        exact hi.comp_aemeasurable measurable_fst.aemeasurable
      have hnew_mix : Integrable
          (fun p : BanditHistory k r × (Fin k × ℝ) ↦
            exp4MixtureStep η E r p.1 p.2)
          (μ.compProd κ) :=
        exp4MixtureStep_integrable_joint
          x hx π η E hE0 hE1 hπ r m₀
      have hold_reward : Integrable
          (fun p : BanditHistory k r × (Fin k × ℝ) ↦
            ∑ t, (p.1 t).2)
          (μ.compProd κ) := by
        have hi : Integrable
            (fun h : BanditHistory k r ↦ ∑ t, (h t).2)
            (Measure.map Prod.fst (μ.compProd κ)) := by
          change Integrable (fun h : BanditHistory k r ↦ ∑ t, (h t).2)
            ((μ.compProd κ).fst)
          rw [Measure.fst_compProd]
          exact ih.2.1
        exact hi.comp_aemeasurable measurable_fst.aemeasurable
      have hnew_reward : Integrable
          (fun p : BanditHistory k r × (Fin k × ℝ) ↦ p.2.2)
          (μ.compProd κ) :=
        rewardStep_integrable_joint_mix x hx π r
      have hmix_comp : Integrable
          ((fun h : BanditHistory k (r + 1) ↦
            exp4MixtureEstimate η E (r + 1) h) ∘ snoc)
          (μ.compProd κ) := by
        change Integrable
          (fun p ↦ exp4MixtureEstimate η E (r + 1) (snoc p))
          (μ.compProd κ)
        rw [hmix_rewrite]
        exact hold_mix.add hnew_mix
      have hreward_comp : Integrable
          ((fun h : BanditHistory k (r + 1) ↦ ∑ t, (h t).2) ∘ snoc)
          (μ.compProd κ) := by
        change Integrable (fun p ↦ ∑ t, ((snoc p) t).2) (μ.compProd κ)
        rw [hreward_rewrite]
        exact hold_reward.add hnew_reward
      constructor
      · rw [adversarialMeasure]
        apply (integrable_map_measure
          (exp4MixtureEstimate_measurable_mix η E (r + 1)).aestronglyMeasurable
          hsnoc.aemeasurable).2
        exact hmix_comp
      constructor
      · rw [adversarialMeasure]
        apply (integrable_map_measure
          rewardSum_measurable_mix.aestronglyMeasurable
          hsnoc.aemeasurable).2
        exact hreward_comp
      · rw [adversarialMeasure,
          integral_map hsnoc.aemeasurable
            (exp4MixtureEstimate_measurable_mix η E (r + 1)).aestronglyMeasurable,
          integral_map hsnoc.aemeasurable
            rewardSum_measurable_mix.aestronglyMeasurable]
        change
          (∫ p, exp4MixtureEstimate η E (r + 1) (snoc p)
              ∂(μ.compProd κ)) =
            ∫ p, (∑ t, ((snoc p) t).2) ∂(μ.compProd κ)
        rw [hmix_rewrite, hreward_rewrite,
          integral_add hold_mix hnew_mix,
          integral_add hold_reward hnew_reward,
          Measure.integral_compProd hold_mix,
          Measure.integral_compProd hnew_mix,
          Measure.integral_compProd hold_reward,
          Measure.integral_compProd hnew_reward]
        simp only [Prod.fst, Prod.snd]
        have hstep (h : BanditHistory k r) :
            (∫ z, exp4MixtureStep η E r h z ∂(κ h)) =
              ∫ z : Fin k × ℝ, z.2 ∂(κ h) := by
          rw [exp4MixtureStep_integral x π η E hE0 hE1 hπ r h m₀,
            rewardStep_integral_mix x π η E hE0 hπ r h]
        simp_rw [hstep]
        have hold_eq :
            (∫ h, exp4MixtureEstimate η E r h ∂μ) =
              ∫ h, (∑ t, (h t).2) ∂μ := by
          simpa [μ] using ih.2.2
        simpa using congrArg
          (fun z : ℝ ↦ z +
            ∫ h, (∫ z : Fin k × ℝ, z.2 ∂(κ h)) ∂μ) hold_eq

end BanditAlgorithm

theorem solution
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp4Policy η 0 E π) :
    (∫ h, BanditAlgorithm.exp4MixtureEstimate η E n h
        ∂(BanditAlgorithm.adversarialMeasure x π n)) =
      ∫ h, (∑ t, (h t).2)
        ∂(BanditAlgorithm.adversarialMeasure x π n) := by
  let m₀ : Fin M := ⟨0, by omega⟩
  exact (BanditAlgorithm.exp4MixtureEstimate_integrable_integral_mix
    x hx π η E hE0 hE1 hπ m₀ n).2.2
