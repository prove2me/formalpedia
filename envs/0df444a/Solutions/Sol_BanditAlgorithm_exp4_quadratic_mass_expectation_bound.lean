-- Prove2me | solution 1 for BanditAlgorithm.exp4_quadratic_mass_expectation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T00:28:55.397189+00:00
-- url     : https://prove2.me/submissions/44a843ea-855e-4f90-99b8-99a38e6e57df

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Analysis

/-!
Direct proof of the second-moment calculation in Lattimore--Szepesvári,
*Bandit Algorithms*, Eq. (18.12) and the display immediately below it,
printed p. 230.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private lemma exp4Weights_pos_quad {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (h : BanditHistory k r)
    (m : Fin M) :
    0 < exp4ExpertWeights η 0 E r h m := by
  unfold exp4ExpertWeights expWeights
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨m, Finset.mem_univ _, Real.exp_pos _⟩

private lemma exp4Prob_nonneg_quad {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (r : ℕ) (h : BanditHistory k r) (a : Fin k) :
    0 ≤ exp4Prob η 0 E r h a := by
  unfold exp4Prob
  exact Finset.sum_nonneg fun m _ ↦
    mul_nonneg (exp4Weights_pos_quad η E r h m).le (hE0 r m a)

private lemma exp4Estimate_measurable_quad {k M : ℕ} (η : ℝ)
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
          exact (measurableSet_singleton a).preimage (measurable_fst.comp hlast)
        have hfrac : Measurable
            (fun h : BanditHistory k (r + 1) ↦
              (1 - (h (Fin.last r)).2) /
                exp4Prob η 0 E r (Fin.init h) a) :=
          (measurable_const.sub (measurable_snd.comp hlast)).div (hprob a)
        exact Measurable.ite hcond hfrac measurable_const
      simpa only [exp4Estimate, exp4Prob, exp4ExpertWeights, add_zero, Pi.add_def] using
        hold.add hinc

private lemma exp4Prob_measurable_quad {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (a : Fin k) :
    Measurable (fun h : BanditHistory k r ↦ exp4Prob η 0 E r h a) := by
  unfold exp4Prob exp4ExpertWeights expWeights
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.mul
  · apply Measurable.div
    · exact Real.continuous_exp.measurable.comp
        (measurable_const.mul (exp4Estimate_measurable_quad η E r m))
    · apply Finset.measurable_sum
      intro j hj
      exact Real.continuous_exp.measurable.comp
        (measurable_const.mul (exp4Estimate_measurable_quad η E r j))
  · exact measurable_const

private lemma exp4RewardIncrement_measurable_quad {k M : ℕ} (η : ℝ)
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
    exact (measurableSet_singleton a).preimage measurable_fst
  have hthen : Measurable (fun z : Fin k × ℝ ↦
      (1 - z.2) / exp4Prob η 0 E r h a) :=
    (measurable_const.sub measurable_snd).div_const _
  exact Measurable.ite hset hthen measurable_const

private lemma exp4RewardIncrement_joint_measurable_quad {k M : ℕ} (η : ℝ)
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
    exact (measurableSet_singleton a).preimage
        (measurable_fst.comp measurable_snd)
  have hfrac : Measurable
      (fun p : BanditHistory k r × (Fin k × ℝ) ↦
        (1 - p.2.2) / exp4Prob η 0 E r p.1 a) :=
    (measurable_const.sub (measurable_snd.comp measurable_snd)).div
      ((exp4Prob_measurable_quad η E r a).comp measurable_fst)
  exact Measurable.ite hcond hfrac measurable_const

private noncomputable def exp4QuadraticStep {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (z : Fin k × ℝ) : ℝ :=
  ∑ m, exp4ExpertWeights η 0 E r h m *
    (1 - exp4RewardIncrement η E r h m z) ^ 2

private lemma exp4QuadraticStep_nonneg {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (z : Fin k × ℝ) :
    0 ≤ exp4QuadraticStep η E r h z := by
  unfold exp4QuadraticStep
  exact Finset.sum_nonneg fun m _ ↦
    mul_nonneg (exp4Weights_pos_quad η E r h m).le (sq_nonneg _)

private lemma exp4QuadraticStep_measurable {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) :
    Measurable (exp4QuadraticStep η E r h) := by
  unfold exp4QuadraticStep
  exact Finset.measurable_sum _ fun m _ ↦
    measurable_const.mul
      ((measurable_const.sub
        (exp4RewardIncrement_measurable_quad η E r h m)).pow_const 2)

private lemma exp4QuadraticStep_joint_measurable {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) :
    Measurable (fun p : BanditHistory k r × (Fin k × ℝ) ↦
      exp4QuadraticStep η E r p.1 p.2) := by
  unfold exp4QuadraticStep
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.mul
  · unfold exp4ExpertWeights expWeights
    apply Measurable.div
    · exact Real.continuous_exp.measurable.comp
        (measurable_const.mul
          ((exp4Estimate_measurable_quad η E r m).comp measurable_fst))
    · apply Finset.measurable_sum
      intro j hj
      exact Real.continuous_exp.measurable.comp
        (measurable_const.mul
          ((exp4Estimate_measurable_quad η E r j).comp measurable_fst))
  · exact (measurable_const.sub
      (exp4RewardIncrement_joint_measurable_quad η E r m)).pow_const 2

private lemma exp4RewardIncrement_action_quad {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (r : ℕ) (h : BanditHistory k r) (m : Fin M)
    (a : Fin k) (y : ℝ) :
    1 - exp4RewardIncrement η E r h m (a, y) =
      E r m a * ((1 - y) / exp4Prob η 0 E r h a) := by
  classical
  unfold exp4RewardIncrement
  have hscore :
      (∑ b, E r m b *
        (1 - if a = b then
          (1 - y) / exp4Prob η 0 E r h b
        else 0)) =
        1 - E r m a * ((1 - y) / exp4Prob η 0 E r h a) := by
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
  rw [hscore]
  ring

private lemma advice_le_one_quad {k M : ℕ}
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (r : ℕ) (m : Fin M) (a : Fin k) :
    E r m a ≤ 1 := by
  calc
    E r m a ≤ ∑ b, E r m b :=
      Finset.single_le_sum (fun b _ ↦ hE0 r m b) (Finset.mem_univ a)
    _ = 1 := hE1 r m

private lemma exp4QuadraticStep_integrable_step {k M : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (r : ℕ) (h : BanditHistory k r) :
    Integrable (exp4QuadraticStep η E r h)
      (adversarialStepKernel x π r h) := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  apply (integrable_map_measure
    (exp4QuadraticStep_measurable η E r h).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  exact Integrable.of_finite

private lemma exp4QuadraticStep_integral_le_card {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (h : BanditHistory k r) :
    (∫ z, exp4QuadraticStep η E r h z
      ∂(adversarialStepKernel x π r h)) ≤ k := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp4QuadraticStep_measurable η E r h).aestronglyMeasurable]
  rw [hπ r h, integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ a : Fin k,
        (ENNReal.ofReal (exp4Prob η 0 E r h a)).toReal =
          exp4Prob η 0 E r h a :=
      fun a ↦ ENNReal.toReal_ofReal
        (exp4Prob_nonneg_quad η E hE0 r h a)
    simp_rw [htoReal]
    calc
      (∑ a, exp4Prob η 0 E r h a *
          exp4QuadraticStep η E r h (a, x r a)) ≤
          ∑ _a : Fin k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        have hp0 : 0 ≤ exp4Prob η 0 E r h a :=
          exp4Prob_nonneg_quad η E hE0 r h a
        by_cases hpzero : exp4Prob η 0 E r h a = 0
        · simp [hpzero]
        · have hp : 0 < exp4Prob η 0 E r h a :=
            lt_of_le_of_ne hp0 (Ne.symm hpzero)
          unfold exp4QuadraticStep
          simp_rw [exp4RewardIncrement_action_quad η E hE1 r h]
          rw [Finset.mul_sum]
          calc
            (∑ m, exp4Prob η 0 E r h a *
                (exp4ExpertWeights η 0 E r h m *
                  (E r m a *
                    ((1 - x r a) / exp4Prob η 0 E r h a)) ^ 2)) =
                ∑ m, exp4ExpertWeights η 0 E r h m *
                  ((E r m a * (1 - x r a)) ^ 2 /
                    exp4Prob η 0 E r h a) := by
              apply Finset.sum_congr rfl
              intro m hm
              field_simp [ne_of_gt hp]
            _ ≤ ∑ m, exp4ExpertWeights η 0 E r h m *
                  (E r m a / exp4Prob η 0 E r h a) := by
              apply Finset.sum_le_sum
              intro m hm
              have hE0ma : 0 ≤ E r m a := hE0 r m a
              have hE1ma : E r m a ≤ 1 :=
                advice_le_one_quad E hE0 hE1 r m a
              have hl0 : 0 ≤ 1 - x r a :=
                sub_nonneg.mpr (hx r a).2
              have hl1 : 1 - x r a ≤ 1 := by
                linarith [(hx r a).1]
              have hprod0 : 0 ≤ E r m a * (1 - x r a) :=
                mul_nonneg hE0ma hl0
              have hprod_le : E r m a * (1 - x r a) ≤ E r m a :=
                mul_le_of_le_one_right hE0ma hl1
              have hsquare1 :=
                mul_self_le_mul_self hprod0 hprod_le
              have hsquare2 : E r m a * E r m a ≤ E r m a := by
                nlinarith [mul_nonneg hE0ma (sub_nonneg.mpr hE1ma)]
              have hsquare :
                  (E r m a * (1 - x r a)) ^ 2 ≤ E r m a := by
                nlinarith
              exact mul_le_mul_of_nonneg_left
                ((div_le_div_iff_of_pos_right hp).2 hsquare)
                (exp4Weights_pos_quad η E r h m).le
            _ = ∑ m, (exp4ExpertWeights η 0 E r h m * E r m a) /
                  exp4Prob η 0 E r h a := by
              apply Finset.sum_congr rfl
              intro m hm
              ring
            _ = (∑ m, exp4ExpertWeights η 0 E r h m * E r m a) /
                  exp4Prob η 0 E r h a := by
              rw [Finset.sum_div]
            _ = exp4Prob η 0 E r h a / exp4Prob η 0 E r h a := by
              rfl
            _ = 1 := div_self hp.ne'
      _ = k := by simp
  · intro a ha
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp4QuadraticStep_norm_integral_le_card {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (h : BanditHistory k r) :
    (∫ z, ‖exp4QuadraticStep η E r h z‖
      ∂(adversarialStepKernel x π r h)) ≤ k := by
  have heq :
      (∫ z, ‖exp4QuadraticStep η E r h z‖
        ∂(adversarialStepKernel x π r h)) =
      ∫ z, exp4QuadraticStep η E r h z
        ∂(adversarialStepKernel x π r h) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ by
      change ‖exp4QuadraticStep η E r h z‖ =
        exp4QuadraticStep η E r h z
      rw [Real.norm_eq_abs,
        abs_of_nonneg (exp4QuadraticStep_nonneg η E r h z)]
  rw [heq]
  exact exp4QuadraticStep_integral_le_card
    x hx π η E hE0 hE1 hπ r h

private lemma exp4QuadraticStep_integrable_joint {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π) (r : ℕ) :
    Integrable
      (fun p : BanditHistory k r × (Fin k × ℝ) ↦
        exp4QuadraticStep η E r p.1 p.2)
      ((adversarialMeasure x π r).compProd
        (adversarialStepKernel x π r)) := by
  apply (Measure.integrable_compProd_iff
    (exp4QuadraticStep_joint_measurable η E r).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      exp4QuadraticStep_integrable_step x π η E r h
  · apply Integrable.of_mem_Icc 0 k
    · exact (exp4QuadraticStep_joint_measurable η E r).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun z ↦ norm_nonneg _)
        · exact exp4QuadraticStep_norm_integral_le_card
            x hx π η E hE0 hE1 hπ r h

private lemma exp4QuadraticMass_measurable_quad {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) :
    ∀ r : ℕ,
      Measurable (fun h : BanditHistory k r ↦
        exp4QuadraticMass η E r h) := by
  intro r
  induction r with
  | zero =>
      simp [exp4QuadraticMass]
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
      simpa only [exp4QuadraticMass, exp4QuadraticStep, Pi.add_def, Function.comp_def] using
        (ih.comp hinit).add
          ((exp4QuadraticStep_joint_measurable η E r).comp hpair)

private theorem exp4QuadraticMass_integrable_integral_le {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π) :
    ∀ r : ℕ,
      Integrable (fun h : BanditHistory k r ↦
        exp4QuadraticMass η E r h) (adversarialMeasure x π r) ∧
      (∫ h, exp4QuadraticMass η E r h
          ∂(adversarialMeasure x π r)) ≤ (r : ℝ) * k := by
  intro r
  induction r with
  | zero =>
      simp [exp4QuadraticMass, adversarialMeasure]
  | succ r ih =>
      let μ := adversarialMeasure x π r
      let κ := adversarialStepKernel x π r
      let snoc : BanditHistory k r × (Fin k × ℝ) →
          BanditHistory k (r + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      have hsnoc : Measurable snoc := measurable_banditHistorySnoc
      have hrewrite :
          (fun p ↦ exp4QuadraticMass η E (r + 1) (snoc p)) =
            fun p ↦ exp4QuadraticMass η E r p.1 +
              exp4QuadraticStep η E r p.1 p.2 := by
        funext p
        simp [snoc, exp4QuadraticMass, exp4QuadraticStep]
      have hold : Integrable
          (fun p : BanditHistory k r × (Fin k × ℝ) ↦
            exp4QuadraticMass η E r p.1)
          (μ.compProd κ) := by
        have hi : Integrable
            (fun h : BanditHistory k r ↦ exp4QuadraticMass η E r h)
            (Measure.map Prod.fst (μ.compProd κ)) := by
          change Integrable
            (fun h : BanditHistory k r ↦ exp4QuadraticMass η E r h)
            ((μ.compProd κ).fst)
          rw [Measure.fst_compProd]
          exact ih.1
        exact hi.comp_aemeasurable measurable_fst.aemeasurable
      have hnew : Integrable
          (fun p : BanditHistory k r × (Fin k × ℝ) ↦
            exp4QuadraticStep η E r p.1 p.2)
          (μ.compProd κ) :=
        exp4QuadraticStep_integrable_joint
          x hx π η E hE0 hE1 hπ r
      have hcomp : Integrable
          ((fun h : BanditHistory k (r + 1) ↦
            exp4QuadraticMass η E (r + 1) h) ∘ snoc)
          (μ.compProd κ) := by
        change Integrable
          (fun p ↦ exp4QuadraticMass η E (r + 1) (snoc p))
          (μ.compProd κ)
        rw [hrewrite]
        exact hold.add hnew
      constructor
      · rw [adversarialMeasure]
        apply (integrable_map_measure
          (exp4QuadraticMass_measurable_quad η E (r + 1)).aestronglyMeasurable
          hsnoc.aemeasurable).2
        exact hcomp
      · rw [adversarialMeasure,
          integral_map hsnoc.aemeasurable
            (exp4QuadraticMass_measurable_quad η E
              (r + 1)).aestronglyMeasurable]
        change
          (∫ p, exp4QuadraticMass η E (r + 1) (snoc p)
              ∂(μ.compProd κ)) ≤ ((r + 1 : ℕ) : ℝ) * (k : ℝ)
        rw [hrewrite, integral_add hold hnew,
          Measure.integral_compProd hold, Measure.integral_compProd hnew]
        simp_rw [integral_const]
        have hkappa (h : BanditHistory k r) : (κ h).real Set.univ = 1 := by
          simp [κ]
        simp_rw [hkappa, one_smul]
        have hinner : Integrable
            (fun h : BanditHistory k r ↦
              ∫ z, exp4QuadraticStep η E r h z ∂(κ h)) μ :=
          hnew.integral_compProd
        have hinner_le :
            (∫ h, (∫ z, exp4QuadraticStep η E r h z ∂(κ h)) ∂μ) ≤
              (k : ℝ) := by
          calc
            _ ≤ ∫ _h : BanditHistory k r, (k : ℝ) ∂μ := by
              apply integral_mono hinner (integrable_const _)
              intro h
              simpa [κ] using
                exp4QuadraticStep_integral_le_card
                  x hx π η E hE0 hE1 hπ r h
            _ = k := by simp
        have hold_le :
            (∫ h, exp4QuadraticMass η E r h ∂μ) ≤
              (r : ℝ) * k := by
          simpa [μ] using ih.2
        norm_num at hold_le hinner_le ⊢
        nlinarith

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
    (∫ h, BanditAlgorithm.exp4QuadraticMass η E n h
      ∂(BanditAlgorithm.adversarialMeasure x π n)) ≤
      (n : ℝ) * k := by
  exact (BanditAlgorithm.exp4QuadraticMass_integrable_integral_le
    x hx π η E hE0 hE1 hπ n).2
