-- Prove2me | solution 1 for BanditAlgorithm.exp3_estimate_advantage_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-18T21:28:39.927291+00:00
-- url     : https://prove2.me/submissions/107f8479-8d0b-468f-8b8c-bf0ed451ce92

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Verified analytic ingredient for the remaining Exp3 advantage theorem.
This is the shifted quadratic exponential bound used in
Lattimore--Szepesvári, *Bandit Algorithms*, Theorem 11.2,
printed p. 156 immediately before Eq. (11.15).
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private lemma exp_le_quadratic_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun y ↦ 1 + y + y ^ 2 / 2 - Real.exp y
  have hfderiv : ∀ y : ℝ, HasDerivAt f (1 + y - Real.exp y) y := by
    intro y
    dsimp [f]
    convert ((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
      ((hasDerivAt_id y).pow 2 |>.div_const 2)).sub (Real.hasDerivAt_exp y)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring) | (funext z; simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)
  have hfanti : Antitone f := by
    apply antitone_of_hasDerivAt_nonpos hfderiv
    intro y
    change 1 + y - Real.exp y ≤ 0
    linarith [Real.add_one_le_exp y]
  have hmono := hfanti hx
  dsimp [f] at hmono ⊢
  norm_num at hmono
  linarith

private lemma exp_scaled_le_shifted_quadratic
    (η y : ℝ) (hη : 0 ≤ η) (hy : y ≤ 1) :
    Real.exp (η * y) ≤
      Real.exp η * (1 + η * (y - 1) + (η ^ 2 / 2) * (y - 1) ^ 2) := by
  rw [show η * y = η + η * (y - 1) by ring, Real.exp_add]
  gcongr
  convert exp_le_quadratic_of_nonpos (η * (y - 1)) (mul_nonpos_of_nonneg_of_nonpos hη (by linarith)) using 1 <;>
    first | rfl | ring

/-- The one-round exponential-potential estimate used to pass from Eq. (11.11)
to the sharpened potential inequality on printed p. 156. -/
private lemma weighted_exp_sum_le_potential
    {k : ℕ} (p y : Fin k → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hy : ∀ j, y j ≤ 1) :
    (∑ j, p j * Real.exp (η * y j)) ≤
      Real.exp (η * ∑ j, p j * y j +
        (η ^ 2 / 2) * ∑ j, p j * (y j - 1) ^ 2) := by
  classical
  have hshift : (∑ j, p j * (y j - 1)) = (∑ j, p j * y j) - 1 := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hsum]
  let z := η * (∑ j, p j * (y j - 1)) +
    (η ^ 2 / 2) * ∑ j, p j * (y j - 1) ^ 2
  calc
    (∑ j, p j * Real.exp (η * y j)) ≤
        Real.exp η * ∑ j, p j *
          (1 + η * (y j - 1) + (η ^ 2 / 2) * (y j - 1) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left
          (exp_scaled_le_shifted_quadratic η (y j) hη (hy j)) (hp j)
    _ = Real.exp η * (1 + z) := by
      dsimp [z]
      have hsum_expand :
          (∑ j, p j *
            (1 + η * (y j - 1) + (η ^ 2 / 2) * (y j - 1) ^ 2)) =
            (∑ j, p j) + η * (∑ j, p j * (y j - 1)) +
              (η ^ 2 / 2) * (∑ j, p j * (y j - 1) ^ 2) := by
        calc
          _ = ∑ j, (p j + η * (p j * (y j - 1)) +
              (η ^ 2 / 2) * (p j * (y j - 1) ^ 2)) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = (∑ j, p j) + (∑ j, η * (p j * (y j - 1))) +
              ∑ j, (η ^ 2 / 2) * (p j * (y j - 1) ^ 2) := by
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
      rw [hsum_expand, hsum]
      ring
    _ ≤ Real.exp η * Real.exp z :=
      mul_le_mul_of_nonneg_left (by simpa [add_comm] using Real.add_one_le_exp z)
        (Real.exp_pos η).le
    _ = Real.exp (η * ∑ j, p j * y j +
        (η ^ 2 / 2) * ∑ j, p j * (y j - 1) ^ 2) := by
      rw [← Real.exp_add]
      dsimp [z]
      rw [hshift]
      ring

private lemma expWeights_pos_adv {k : ℕ} (s : Fin k → ℝ) (i : Fin k) :
    0 < expWeights s i := by
  rw [expWeights]
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, Real.exp_pos _⟩

private lemma exp3Prob_pos_adv {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) : 0 < exp3Prob η m h i :=
  expWeights_pos_adv _ i

private lemma exp3Prob_sum_adv {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) : ∑ j, exp3Prob η m h j = 1 := by
  rw [show (∑ j, exp3Prob η m h j) =
      (∑ j, Real.exp (η * exp3Estimate η m h j)) /
        (∑ j, Real.exp (η * exp3Estimate η m h j)) by
    simp only [exp3Prob, expWeights, Finset.sum_div]]
  exact div_self (ne_of_gt (Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, Real.exp_pos _⟩))

private noncomputable def exp3RewardIncrement {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) (z : Fin k × ℝ) : ℝ :=
  1 - if z.1 = i then (1 - z.2) / exp3Prob η m h i else 0

private lemma exp3RewardIncrement_le_one {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) (z : Fin k × ℝ) (hz : z.2 ≤ 1) :
    exp3RewardIncrement η m h i z ≤ 1 := by
  by_cases hzi : z.1 = i
  · simp only [exp3RewardIncrement, if_pos hzi]
    have hnum : 0 ≤ 1 - z.2 := sub_nonneg.mpr hz
    have hden : 0 ≤ exp3Prob η m h i := (exp3Prob_pos_adv η m h i).le
    exact sub_le_self _ (div_nonneg hnum hden)
  · simp [exp3RewardIncrement, hzi]

private lemma exp3RewardIncrement_measurable_adv {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) :
    Measurable (exp3RewardIncrement η m h i) := by
  letI : DecidableEq (Fin k) := Classical.decEq _
  unfold exp3RewardIncrement
  apply Measurable.sub measurable_const
  have hnum : Measurable (fun z : Fin k × ℝ ↦ (1 : ℝ) - z.2) :=
    measurable_const.sub measurable_snd
  have hset : MeasurableSet {z : Fin k × ℝ | z.1 = i} := by
    exact
      (measurableSet_singleton i).preimage measurable_fst
  exact Measurable.ite hset (hnum.div_const _) measurable_const

/-- Pointwise identity behind Eq. (11.9): the Exp3 probability-weighted sum
of the loss-based reward estimates is exactly the observed reward. -/
private lemma exp3_prob_weighted_increment_eq_reward_adv
    {k : ℕ} (η : ℝ) (m : ℕ) (h : BanditHistory k m)
    (z : Fin k × ℝ) (i0 : Fin k) :
    (∑ j, exp3Prob η m h j * exp3RewardIncrement η m h j z) = z.2 := by
  classical
  have hp : 0 < exp3Prob η m h z.1 := exp3Prob_pos_adv η m h z.1
  have hsum : ∑ j, exp3Prob η m h j = 1 := exp3Prob_sum_adv η m h i0
  have hdecomp :
      (∑ j, exp3Prob η m h j * exp3RewardIncrement η m h j z) =
        (∑ j, exp3Prob η m h j) -
          exp3Prob η m h z.1 * ((1 - z.2) / exp3Prob η m h z.1) := by
    calc
      _ = (∑ j, exp3Prob η m h j) -
          ∑ j, if z.1 = j then
            exp3Prob η m h z.1 * ((1 - z.2) / exp3Prob η m h z.1)
          else 0 := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hzj : z.1 = j
            · subst j
              simp [exp3RewardIncrement]
              ring
            · simp [exp3RewardIncrement, hzj]
      _ = _ := by simp
  rw [hdecomp, hsum]
  field_simp
  ring

private lemma exp3Estimate_snoc_adv {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) (i : Fin k) :
    exp3Estimate η (m + 1) (Fin.snoc h z) i =
      exp3Estimate η m h i + exp3RewardIncrement η m h i z := by
  simp [exp3Estimate, exp3RewardIncrement, exp3Prob]

/-- The exact exponential-potential ratio identity, Eq. (11.11), for an
arbitrary score vector and one-round increment vector. -/
private lemma expWeights_potential_ratio_adv
    {k : ℕ} (η : ℝ) (s y : Fin k → ℝ) :
    (∑ j, Real.exp (η * (s j + y j))) / (∑ j, Real.exp (η * s j)) =
      ∑ j, expWeights (fun a ↦ η * s a) j * Real.exp (η * y j) := by
  simp only [expWeights]
  rw [show (∑ j, Real.exp (η * s j) / (∑ a, Real.exp (η * s a)) *
      Real.exp (η * y j)) =
      (∑ j, Real.exp (η * s j) * Real.exp (η * y j)) /
        (∑ a, Real.exp (η * s a)) by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Real.exp_add]
  congr 1
  ring

private lemma exp3_potential_ratio_adv
    {k : ℕ} (η : ℝ) (m : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    (∑ j, Real.exp (η * exp3Estimate η (m + 1) (Fin.snoc h z) j)) /
        (∑ j, Real.exp (η * exp3Estimate η m h j)) =
      ∑ j, exp3Prob η m h j *
        Real.exp (η * exp3RewardIncrement η m h j z) := by
  simp_rw [exp3Estimate_snoc_adv]
  exact expWeights_potential_ratio_adv η
    (fun j ↦ exp3Estimate η m h j)
    (fun j ↦ exp3RewardIncrement η m h j z)

private lemma exp3_potential_zero_adv {k : ℕ} (η : ℝ)
    (h : BanditHistory k 0) :
    (∑ j, Real.exp (η * exp3Estimate η 0 h j)) = k := by
  simp [exp3Estimate]

private lemma exp3_comparator_exp_le_potential_adv
    {k n : ℕ} (η : ℝ) (h : BanditHistory k n) (i : Fin k) :
    Real.exp (η * exp3Estimate η n h i) ≤
      ∑ j, Real.exp (η * exp3Estimate η n h j) := by
  exact Finset.single_le_sum
    (fun j _ ↦ (Real.exp_pos (η * exp3Estimate η n h j)).le)
    (Finset.mem_univ i)

/-- The exact one-step potential estimate for the Exp3 reward increment.
It is the formal counterpart of the displayed inequality on printed p. 156
immediately preceding Eq. (11.15). -/
private lemma exp3_one_step_potential_adv
    {k : ℕ} (η : ℝ) (hη : 0 ≤ η) (m : ℕ) (h : BanditHistory k m)
    (z : Fin k × ℝ) (hz : z.2 ≤ 1) (i0 : Fin k) :
    (∑ j, exp3Prob η m h j *
      Real.exp (η * exp3RewardIncrement η m h j z)) ≤
      Real.exp
        (η * ∑ j, exp3Prob η m h j * exp3RewardIncrement η m h j z +
          (η ^ 2 / 2) * ∑ j, exp3Prob η m h j *
            (exp3RewardIncrement η m h j z - 1) ^ 2) := by
  exact weighted_exp_sum_le_potential
    (fun j ↦ exp3Prob η m h j)
    (fun j ↦ exp3RewardIncrement η m h j z)
    η hη (fun j ↦ (exp3Prob_pos_adv η m h j).le)
    (exp3Prob_sum_adv η m h i0)
    (fun j ↦ exp3RewardIncrement_le_one η m h j z hz)

/-- The pointwise quadratic-to-loss estimate in the proof of Theorem 11.2,
printed p. 156: `P_j (Xhat_j - 1)^2 ≤ Yhat_j`, summed over arms. -/
private lemma exp3_quadratic_le_loss_sum_adv
    {k : ℕ} (η : ℝ) (m : ℕ) (h : BanditHistory k m)
    (z : Fin k × ℝ) (hz0 : 0 ≤ z.2) (hz1 : z.2 ≤ 1) :
    (∑ j, exp3Prob η m h j *
      (exp3RewardIncrement η m h j z - 1) ^ 2) ≤
      ∑ j, (1 - exp3RewardIncrement η m h j z) := by
  classical
  apply Finset.sum_le_sum
  intro j hj
  by_cases hzj : z.1 = j
  · simp only [exp3RewardIncrement, if_pos hzj]
    have hp : 0 < exp3Prob η m h j := exp3Prob_pos_adv η m h j
    have hl0 : 0 ≤ 1 - z.2 := by linarith
    have hl1 : 1 - z.2 ≤ 1 := by linarith
    field_simp
    nlinarith [mul_self_le_mul_self hl0 hl1]
  · simp [exp3RewardIncrement, hzj]

/-- Conditional expectation of the total loss-estimator mass. This is the
calculation used immediately after Eq. (11.15), printed pp. 156--157. -/
private lemma exp3_loss_sum_integral_step_adv
    {k : ℕ} (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (hπ : IsExp3Policy η π) (m : ℕ) (h : BanditHistory k m) :
    (∫ z, (∑ j, (1 - exp3RewardIncrement η m h j z))
      ∂(adversarialStepKernel x π m h)) = ∑ j, (1 - x m j) := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  rw [integral_map (measurable_of_countable _).aemeasurable
    (f := fun z : Fin k × ℝ ↦ ∑ j, (1 - exp3RewardIncrement η m h j z))
    ((Finset.measurable_sum _ fun j _ ↦
      measurable_const.sub (exp3RewardIncrement_measurable_adv η m h j))
      |>.aestronglyMeasurable)]
  rw [hπ m h]
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ a : Fin k,
        (ENNReal.ofReal (exp3Prob η m h a)).toReal = exp3Prob η m h a :=
      fun a ↦ ENNReal.toReal_ofReal (exp3Prob_pos_adv η m h a).le
    simp_rw [htoReal]
    calc
      (∑ a, exp3Prob η m h a *
          ∑ j, (1 - exp3RewardIncrement η m h j (a, x m a))) =
          ∑ a, (1 - x m a) := by
            apply Finset.sum_congr rfl
            intro a ha
            have hp : 0 < exp3Prob η m h a := exp3Prob_pos_adv η m h a
            rw [show (∑ j, (1 - exp3RewardIncrement η m h j (a, x m a))) =
                (1 - x m a) / exp3Prob η m h a by
              have hsingle :
                  1 - exp3RewardIncrement η m h a (a, x m a) =
                    (1 - x m a) / exp3Prob η m h a := by
                simp [exp3RewardIncrement]
              rw [← hsingle]
              apply Finset.sum_eq_single a
              · intro j hj hja
                simp [exp3RewardIncrement, Ne.symm hja]
              · intro ha_not
                exact (ha_not (Finset.mem_univ a)).elim]
            field_simp
      _ = _ := rfl
  · intro a ha
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp3_loss_sum_integral_step_le_card_adv
    {k : ℕ} (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π)
    (m : ℕ) (h : BanditHistory k m) :
    (∫ z, (∑ j, (1 - exp3RewardIncrement η m h j z))
      ∂(adversarialStepKernel x π m h)) ≤ k := by
  rw [exp3_loss_sum_integral_step_adv x π η hπ m h]
  calc
    (∑ j, (1 - x m j)) ≤ ∑ _j : Fin k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      linarith [(hx m j).1]
    _ = k := by simp

/-- Fully specialized one-round inequality used in the telescoping proof of
Eq. (11.15). The linear term is the observed reward and the quadratic term
is reduced to the total loss-estimator mass. -/
private lemma exp3_potential_ratio_le_adv
    {k : ℕ} (η : ℝ) (hη : 0 ≤ η) (m : ℕ) (h : BanditHistory k m)
    (z : Fin k × ℝ) (hz0 : 0 ≤ z.2) (hz1 : z.2 ≤ 1) (i0 : Fin k) :
    (∑ j, Real.exp (η * exp3Estimate η (m + 1) (Fin.snoc h z) j)) /
        (∑ j, Real.exp (η * exp3Estimate η m h j)) ≤
      Real.exp (η * z.2 + (η ^ 2 / 2) *
        ∑ j, (1 - exp3RewardIncrement η m h j z)) := by
  rw [exp3_potential_ratio_adv]
  calc
    (∑ j, exp3Prob η m h j *
        Real.exp (η * exp3RewardIncrement η m h j z)) ≤
      Real.exp
        (η * ∑ j, exp3Prob η m h j * exp3RewardIncrement η m h j z +
          (η ^ 2 / 2) * ∑ j, exp3Prob η m h j *
            (exp3RewardIncrement η m h j z - 1) ^ 2) :=
        exp3_one_step_potential_adv η hη m h z hz1 i0
    _ ≤ Real.exp (η * z.2 + (η ^ 2 / 2) *
        ∑ j, (1 - exp3RewardIncrement η m h j z)) := by
      apply Real.exp_le_exp.mpr
      rw [exp3_prob_weighted_increment_eq_reward_adv η m h z i0]
      have hmul := mul_le_mul_of_nonneg_left
        (exp3_quadratic_le_loss_sum_adv η m h z hz0 hz1)
        (show 0 ≤ η ^ 2 / 2 by positivity)
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hmul (η * z.2)

end BanditAlgorithm
namespace BanditAlgorithm
private lemma expWeights_pos_test {k : ℕ} (s : Fin k → ℝ) (i : Fin k) :
    0 < expWeights s i := by
  rw [expWeights]
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le) ⟨i, Finset.mem_univ _, Real.exp_pos _⟩

private lemma sum_expWeights_test {k : ℕ} (s : Fin k → ℝ) (i : Fin k) :
    ∑ j, expWeights s j = 1 := by
  rw [show (∑ j, expWeights s j) = (∑ j, Real.exp (s j)) / (∑ j, Real.exp (s j)) by
    simp only [expWeights, Finset.sum_div]]
  exact div_self (ne_of_gt (Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, Real.exp_pos _⟩))

private noncomputable def exp3Increment {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) (z : Fin k × ℝ) : ℝ :=
  1 - if z.1 = i then
    (1 - z.2) / exp3Prob η m h i
  else 0

private lemma exp3Increment_measurable {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) :
    Measurable (exp3Increment η m h i) := by
  letI : DecidableEq (Fin k) := Classical.decEq _
  unfold exp3Increment
  apply Measurable.sub measurable_const
  have hnum : Measurable (fun z : Fin k × ℝ ↦ (1 : ℝ) - z.2) :=
    measurable_const.sub measurable_snd
  have hset : MeasurableSet {z : Fin k × ℝ | z.1 = i} := by
    exact
      (measurableSet_singleton i).preimage measurable_fst
  have hthen : Measurable (fun z : Fin k × ℝ ↦
      (1 - z.2) / exp3Prob η m h i) := hnum.div_const _
  exact Measurable.ite hset hthen measurable_const

private lemma exp3Increment_integrable_step {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (hπ : IsExp3Policy η π) (m : ℕ) (h : BanditHistory k m) (i : Fin k) :
    Integrable (exp3Increment η m h i) (adversarialStepKernel x π m h) := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  apply (integrable_map_measure
    (exp3Increment_measurable η m h i).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  exact Integrable.of_finite

private lemma exp3Increment_integral_step {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (hπ : IsExp3Policy η π) (m : ℕ) (h : BanditHistory k m) (i : Fin k) :
    ∫ z, exp3Increment η m h i z ∂(adversarialStepKernel x π m h) = x m i := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp3Increment_measurable η m h i).aestronglyMeasurable]
  rw [hπ m h]
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have hp : 0 < exp3Prob η m h i := expWeights_pos_test _ i
    have hsum : ∑ j, exp3Prob η m h j = 1 := sum_expWeights_test _ i
    have htoReal : ∀ j : Fin k,
        (ENNReal.ofReal (exp3Prob η m h j)).toReal = exp3Prob η m h j :=
      fun j ↦ ENNReal.toReal_ofReal (expWeights_pos_test _ j).le
    simp_rw [htoReal]
    have hdecomp :
        (∑ j, exp3Prob η m h j *
          exp3Increment η m h i (j, x m j)) =
        (∑ j, exp3Prob η m h j) -
          exp3Prob η m h i * ((1 - x m i) / exp3Prob η m h i) := by
      calc
        (∑ j, exp3Prob η m h j * exp3Increment η m h i (j, x m j)) =
            (∑ j, exp3Prob η m h j) -
              ∑ j, if j = i then
                exp3Prob η m h i * ((1 - x m i) / exp3Prob η m h i)
              else 0 := by
                change (∑ j ∈ Finset.univ, exp3Prob η m h j *
                    exp3Increment η m h i (j, x m j)) =
                  (∑ j ∈ Finset.univ, exp3Prob η m h j) -
                    ∑ j ∈ Finset.univ, if j = i then
                      exp3Prob η m h i * ((1 - x m i) / exp3Prob η m h i)
                    else 0
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j = i
                · subst j
                  simp [exp3Increment]
                  ring
                · simp [exp3Increment, hji]
        _ = (∑ j, exp3Prob η m h j) -
              exp3Prob η m h i * ((1 - x m i) / exp3Prob η m h i) := by
                simp
    rw [hdecomp, hsum]
    field_simp
    ring
  · intro j hj
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp3Estimate_measurable_test {k : ℕ} (η : ℝ) :
    ∀ (m : ℕ) (i : Fin k),
      Measurable (fun h : BanditHistory k m ↦ exp3Estimate η m h i) := by
  intro m
  induction m with
  | zero =>
      intro i
      simp [exp3Estimate]
  | succ m ih =>
      intro i
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hold : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            exp3Estimate η m (Fin.init h) i) := (ih i).comp hinit
      have hprob : Measurable
          (fun h : BanditHistory k (m + 1) ↦ exp3Prob η m (Fin.init h) i) := by
        unfold exp3Prob expWeights
        apply Measurable.div
        · exact Real.continuous_exp.measurable.comp
            (measurable_const.mul ((ih i).comp hinit))
        · apply Finset.measurable_sum
          intro j hj
          exact Real.continuous_exp.measurable.comp
            (measurable_const.mul ((ih j).comp hinit))
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcond : MeasurableSet
          {h : BanditHistory k (m + 1) | (h (Fin.last m)).1 = i} := by
        exact
          (measurableSet_singleton i).preimage (measurable_fst.comp hlast)
      have hfrac : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            (1 - (h (Fin.last m)).2) / exp3Prob η m (Fin.init h) i) :=
        (measurable_const.sub (measurable_snd.comp hlast)).div hprob
      have hinc : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            1 - if (h (Fin.last m)).1 = i then
              (1 - (h (Fin.last m)).2) / exp3Prob η m (Fin.init h) i
            else 0) := by
        apply Measurable.sub measurable_const
        exact Measurable.ite hcond hfrac measurable_const
      simpa only [exp3Estimate, exp3Prob, Pi.add_def] using hold.add hinc

private lemma exp3Prob_measurable_test {k : ℕ} (η : ℝ) (m : ℕ) (i : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ exp3Prob η m h i) := by
  unfold exp3Prob expWeights
  apply Measurable.div
  · exact Real.continuous_exp.measurable.comp
      (measurable_const.mul (exp3Estimate_measurable_test η m i))
  · apply Finset.measurable_sum
    intro j hj
    exact Real.continuous_exp.measurable.comp
      (measurable_const.mul (exp3Estimate_measurable_test η m j))

private lemma exp3Increment_joint_measurable_test {k : ℕ} (η : ℝ) (m : ℕ)
    (i : Fin k) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      exp3Increment η m p.1 i p.2) := by
  classical
  unfold exp3Increment
  have hcond : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | p.2.1 = i} := by
    exact
      (measurableSet_singleton i).preimage (measurable_fst.comp measurable_snd)
  have hfrac : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        (1 - p.2.2) / exp3Prob η m p.1 i) :=
    (measurable_const.sub (measurable_snd.comp measurable_snd)).div
      ((exp3Prob_measurable_test η m i).comp measurable_fst)
  apply Measurable.sub measurable_const
  exact Measurable.ite hcond hfrac measurable_const

private lemma exp3Increment_norm_integral_step_test {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (hπ : IsExp3Policy η π) (m : ℕ) (h : BanditHistory k m) (i : Fin k) :
    ∫ z, ‖exp3Increment η m h i z‖ ∂(adversarialStepKernel x π m h) =
      ∑ j, exp3Prob η m h j * ‖exp3Increment η m h i (j, x m j)‖ := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp3Increment_measurable η m h i).norm.aestronglyMeasurable]
  rw [hπ m h]
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ j : Fin k,
        (ENNReal.ofReal (exp3Prob η m h j)).toReal = exp3Prob η m h j :=
      fun j ↦ ENNReal.toReal_ofReal (expWeights_pos_test _ j).le
    simp_rw [htoReal]
  · intro j hj
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp3Increment_norm_integral_step_le_test {k : ℕ}
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ j : Fin k, x t j ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π)
    (m : ℕ) (h : BanditHistory k m) (i : Fin k) :
    (∫ z, ‖exp3Increment η m h i z‖ ∂(adversarialStepKernel x π m h)) ≤ 2 := by
  classical
  rw [exp3Increment_norm_integral_step_test x π η hπ m h i]
  have hsum : ∑ j, exp3Prob η m h j = 1 := sum_expWeights_test _ i
  calc
    (∑ j, exp3Prob η m h j * ‖exp3Increment η m h i (j, x m j)‖) ≤
        ∑ j, (exp3Prob η m h j + if j = i then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      have hp : 0 < exp3Prob η m h j := expWeights_pos_test _ j
      by_cases hji : j = i
      · subst j
        simp only [if_pos]
        have hxi0 : 0 ≤ 1 - x m i := sub_nonneg.mpr (hx m i).2
        have hxi1 : 1 - x m i ≤ 1 := by linarith [(hx m i).1]
        simp only [exp3Increment, if_pos, Real.norm_eq_abs]
        change exp3Prob η m h i * |1 - (1 - x m i) / exp3Prob η m h i| ≤
          exp3Prob η m h i + 1
        calc
          exp3Prob η m h i * |1 - (1 - x m i) / exp3Prob η m h i| ≤
              exp3Prob η m h i *
                (|1| + |(1 - x m i) / exp3Prob η m h i|) :=
            mul_le_mul_of_nonneg_left (abs_sub _ _) hp.le
          _ = exp3Prob η m h i + (1 - x m i) := by
            rw [abs_one, abs_div, abs_of_nonneg hxi0, abs_of_pos hp]
            field_simp
          _ ≤ exp3Prob η m h i + 1 := by linarith
      · simp [exp3Increment, hji, hp.le]
    _ = 2 := by
      rw [Finset.sum_add_distrib]
      simp [hsum]
      norm_num

private lemma exp3Increment_integrable_joint_test {k : ℕ}
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ j : Fin k, x t j ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π)
    (m : ℕ) (i : Fin k) :
    Integrable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        exp3Increment η m p.1 i p.2)
      ((adversarialMeasure x π m).compProd (adversarialStepKernel x π m)) := by
  apply (Measure.integrable_compProd_iff
    (exp3Increment_joint_measurable_test η m i).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      exp3Increment_integrable_step x π η hπ m h i
  · apply Integrable.of_mem_Icc 0 2
    · exact (exp3Increment_joint_measurable_test η m i).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun z ↦ norm_nonneg _)
        · exact exp3Increment_norm_integral_step_le_test x hx π η hπ m h i

private theorem exp3Estimate_integrable_integral_test {k : ℕ}
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ j : Fin k, x t j ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π) :
    ∀ (m : ℕ) (i : Fin k),
      Integrable (fun h : BanditHistory k m ↦ exp3Estimate η m h i)
          (adversarialMeasure x π m) ∧
        (∫ h, exp3Estimate η m h i ∂(adversarialMeasure x π m)) =
          ∑ t : Fin m, x t i := by
  intro m
  induction m with
  | zero =>
      intro i
      simp [exp3Estimate, adversarialMeasure]
  | succ m ih =>
      intro i
      let μ := adversarialMeasure x π m
      let κ := adversarialStepKernel x π m
      let snoc : BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      have hsnoc : Measurable snoc := measurable_banditHistorySnoc
      have hrewrite :
          (fun p ↦ exp3Estimate η (m + 1) (snoc p) i) =
            fun p ↦ exp3Estimate η m p.1 i + exp3Increment η m p.1 i p.2 := by
        funext p
        simp [snoc, exp3Estimate, exp3Increment, exp3Prob]
      have hold : Integrable
          (fun p : BanditHistory k m × (Fin k × ℝ) ↦ exp3Estimate η m p.1 i)
          (μ.compProd κ) := by
        have hi : Integrable
            (fun h : BanditHistory k m ↦ exp3Estimate η m h i)
            (Measure.map Prod.fst (μ.compProd κ)) := by
          change Integrable (fun h : BanditHistory k m ↦ exp3Estimate η m h i)
            ((μ.compProd κ).fst)
          rw [Measure.fst_compProd]
          exact (ih i).1
        exact hi.comp_aemeasurable measurable_fst.aemeasurable
      have hnew : Integrable
          (fun p : BanditHistory k m × (Fin k × ℝ) ↦ exp3Increment η m p.1 i p.2)
          (μ.compProd κ) := exp3Increment_integrable_joint_test x hx π η hπ m i
      have hsum := hold.add hnew
      have hcomp : Integrable
          ((fun h : BanditHistory k (m + 1) ↦ exp3Estimate η (m + 1) h i) ∘ snoc)
          (μ.compProd κ) := by
        change Integrable (fun p ↦ exp3Estimate η (m + 1) (snoc p) i)
          (μ.compProd κ)
        rw [hrewrite]
        exact hsum
      constructor
      · rw [adversarialMeasure]
        apply (integrable_map_measure
          (exp3Estimate_measurable_test η (m + 1) i).aestronglyMeasurable
          hsnoc.aemeasurable).2
        exact hcomp
      · rw [adversarialMeasure,
          integral_map hsnoc.aemeasurable
            (exp3Estimate_measurable_test η (m + 1) i).aestronglyMeasurable]
        change (∫ p, exp3Estimate η (m + 1) (snoc p) i ∂(μ.compProd κ)) =
          ∑ t : Fin (m + 1), x t i
        rw [hrewrite, integral_add hold hnew,
          Measure.integral_compProd hold, Measure.integral_compProd hnew]
        simp only [Prod.fst, Prod.snd]
        rw [Fin.sum_univ_castSucc]
        simp [μ, κ, (ih i).2, exp3Increment_integral_step x π η hπ]

end BanditAlgorithm
namespace BanditAlgorithm

private def GoodAdversarialHistory {k n : ℕ} (h : BanditHistory k n) : Prop :=
  ∀ t : Fin n, (h t).2 ∈ Set.Icc (0 : ℝ) 1

private lemma measurableSet_goodAdversarialHistory {k n : ℕ} :
    MeasurableSet {h : BanditHistory k n | GoodAdversarialHistory h} := by
  rw [show {h : BanditHistory k n | GoodAdversarialHistory h} =
      ⋂ t : Fin n, (fun h : BanditHistory k n ↦ (h t).2) ⁻¹'
        Set.Icc (0 : ℝ) 1 by
    ext h
    simp only [GoodAdversarialHistory, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage]]
  have hmeas : MeasurableSet (⋂ t : Fin n,
      (fun h : BanditHistory k n ↦ (h t).2) ⁻¹' Set.Icc (0 : ℝ) 1) :=
    MeasurableSet.iInter fun t ↦
      measurableSet_Icc.preimage (measurable_snd.comp (measurable_pi_apply t))
  exact hmeas

private lemma adversarialMeasure_ae_good {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) :
    ∀ n : ℕ, ∀ᵐ h ∂(adversarialMeasure x π n), GoodAdversarialHistory h := by
  intro n
  induction n with
  | zero =>
      exact Filter.Eventually.of_forall fun h t ↦ t.elim0
  | succ n ih =>
      rw [adversarialMeasure]
      apply (ae_map_iff measurable_banditHistorySnoc.aemeasurable
        measurableSet_goodAdversarialHistory).2
      apply Measure.ae_compProd_of_ae_ae
        (measurableSet_goodAdversarialHistory.preimage measurable_banditHistorySnoc)
      filter_upwards [ih] with h hh
      rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
      apply (ae_map_iff (measurable_of_countable _).aemeasurable
        (measurableSet_goodAdversarialHistory.preimage
          (measurable_banditHistorySnoc.comp
            (measurable_const.prodMk measurable_id)))).2
      exact Filter.Eventually.of_forall fun a t ↦ by
        refine Fin.lastCases ?_ (fun s ↦ ?_) t
        · simpa using hx n a
        · simpa using hh s

private lemma rewardSum_measurable {k n : ℕ} :
    Measurable (fun h : BanditHistory k n ↦ ∑ t, (h t).2) := by
  exact Finset.measurable_sum _ fun t _ ↦
    measurable_snd.comp (measurable_pi_apply t)

private lemma rewardSum_integrable {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (n : ℕ) :
    Integrable (fun h : BanditHistory k n ↦ ∑ t, (h t).2)
      (adversarialMeasure x π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact rewardSum_measurable.aemeasurable
  · filter_upwards [adversarialMeasure_ae_good x hx π n] with h hh
    constructor
    · exact Finset.sum_nonneg fun t _ ↦ (hh t).1
    · calc
        (∑ t, (h t).2) ≤ ∑ _t : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ ↦ (hh t).2
        _ = n := by simp

end BanditAlgorithm
namespace BanditAlgorithm

private noncomputable def exp3LossMass {k : ℕ} (η : ℝ) :
    (n : ℕ) → BanditHistory k n → ℝ
  | 0, _ => 0
  | m + 1, h =>
      exp3LossMass η m (Fin.init h) +
        ∑ j, (1 - exp3RewardIncrement η m (Fin.init h) j (h (Fin.last m)))

private lemma exp3LossMass_snoc {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    exp3LossMass η (m + 1) (Fin.snoc h z) =
      exp3LossMass η m h +
        ∑ j, (1 - exp3RewardIncrement η m h j z) := by
  simp [exp3LossMass]

private noncomputable def exp3Potential {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) : ℝ :=
  ∑ j, Real.exp (η * exp3Estimate η m h j)

private lemma exp3Potential_pos {k : ℕ} (hk : 0 < k) (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) : 0 < exp3Potential η m h := by
  unfold exp3Potential
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨Classical.choice (Fin.pos_iff_nonempty.mp hk),
      Finset.mem_univ _, Real.exp_pos _⟩

private lemma exp3_log_potential_bound {k : ℕ} (hk : 0 < k)
    (η : ℝ) (hη : 0 ≤ η) :
    ∀ (m : ℕ) (h : BanditHistory k m),
      (∀ t : Fin m, (h t).2 ∈ Set.Icc (0 : ℝ) 1) →
      Real.log (exp3Potential η m h) ≤
        Real.log k + η * (∑ t, (h t).2) + (η ^ 2 / 2) * exp3LossMass η m h := by
  intro m
  induction m with
  | zero =>
      intro h hh
      simp [exp3Potential, exp3Estimate, exp3LossMass]
  | succ m ih =>
      intro h hh
      let h0 : BanditHistory k m := Fin.init h
      let z : Fin k × ℝ := h (Fin.last m)
      have hh0 : ∀ t : Fin m, (h0 t).2 ∈ Set.Icc (0 : ℝ) 1 := by
        intro t
        exact hh (Fin.castSucc t)
      have hz : z.2 ∈ Set.Icc (0 : ℝ) 1 := hh (Fin.last m)
      have hstep := exp3_potential_ratio_le_adv η hη m h0 z hz.1 hz.2
        (Classical.choice (Fin.pos_iff_nonempty.mp hk))
      have hratio : exp3Potential η (m + 1) h / exp3Potential η m h0 ≤
          Real.exp (η * z.2 + (η ^ 2 / 2) *
            ∑ j, (1 - exp3RewardIncrement η m h0 j z)) := by
        simpa [exp3Potential, h0, z] using hstep
      have hnewpos : 0 < exp3Potential η (m + 1) h := exp3Potential_pos hk η _ h
      have holdpos : 0 < exp3Potential η m h0 := exp3Potential_pos hk η _ h0
      have hlogstep : Real.log (exp3Potential η (m + 1) h) ≤
          Real.log (exp3Potential η m h0) +
            (η * z.2 + (η ^ 2 / 2) *
              ∑ j, (1 - exp3RewardIncrement η m h0 j z)) := by
        have hlogratio :
            Real.log (exp3Potential η (m + 1) h / exp3Potential η m h0) ≤
              η * z.2 + (η ^ 2 / 2) *
                ∑ j, (1 - exp3RewardIncrement η m h0 j z) :=
          (Real.log_le_iff_le_exp (div_pos hnewpos holdpos)).2 hratio
        rw [Real.log_div hnewpos.ne' holdpos.ne'] at hlogratio
        linarith
      have hi := ih h0 hh0
      have hsnoc : h = Fin.snoc h0 z := by simp [h0, z]
      rw [hsnoc, exp3LossMass_snoc]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      calc
        Real.log (exp3Potential η (m + 1) (Fin.snoc h0 z)) ≤
            Real.log (exp3Potential η m h0) +
              (η * z.2 + (η ^ 2 / 2) *
                ∑ j, (1 - exp3RewardIncrement η m h0 j z)) := by
          simpa [hsnoc] using hlogstep
        _ ≤ (Real.log k + η * (∑ t, (h0 t).2) +
              (η ^ 2 / 2) * exp3LossMass η m h0) +
              (η * z.2 + (η ^ 2 / 2) *
                ∑ j, (1 - exp3RewardIncrement η m h0 j z)) :=
          by
            linarith
        _ = _ := by ring

private lemma exp3_pathwise_advantage_bound {k : ℕ} (hk : 1 < k)
    (η : ℝ) (hη : 0 < η) (m : ℕ) (h : BanditHistory k m)
    (hh : ∀ t : Fin m, (h t).2 ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) :
    exp3Estimate η m h i - (∑ t, (h t).2) ≤
      Real.log k / η + η * exp3LossMass η m h / 2 := by
  have hk0 : 0 < k := by omega
  have hcomp : η * exp3Estimate η m h i ≤ Real.log (exp3Potential η m h) := by
    apply (Real.le_log_iff_exp_le (exp3Potential_pos hk0 η m h)).2
    exact exp3_comparator_exp_le_potential_adv η h i
  have hpot := exp3_log_potential_bound hk0 η hη.le m h hh
  have hmain : η * (exp3Estimate η m h i - (∑ t, (h t).2)) ≤
      Real.log k + (η ^ 2 / 2) * exp3LossMass η m h := by
    nlinarith
  calc
    exp3Estimate η m h i - (∑ t, (h t).2) ≤
        (Real.log k + (η ^ 2 / 2) * exp3LossMass η m h) / η :=
      (le_div_iff₀ hη).2 (by simpa [mul_comm] using hmain)
    _ = Real.log k / η + η * exp3LossMass η m h / 2 := by
      field_simp [hη.ne']

end BanditAlgorithm
namespace BanditAlgorithm

private noncomputable def exp3LossStep {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) : ℝ :=
  ∑ j, (1 - exp3RewardIncrement η m h j z)

private lemma exp3LossStep_measurable {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) : Measurable (exp3LossStep η m h) := by
  unfold exp3LossStep
  exact Finset.measurable_sum _ fun j _ ↦
    measurable_const.sub (exp3RewardIncrement_measurable_adv η m h j)

private lemma exp3LossStep_joint_measurable {k : ℕ} (η : ℝ) (m : ℕ) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      exp3LossStep η m p.1 p.2) := by
  unfold exp3LossStep
  apply Finset.measurable_sum
  intro j hj
  apply Measurable.sub measurable_const
  simpa only [exp3Increment, exp3RewardIncrement] using
    exp3Increment_joint_measurable_test η m j

private lemma exp3LossStep_action {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (a : Fin k) (r : ℝ) :
    exp3LossStep η m h (a, r) = (1 - r) / exp3Prob η m h a := by
  classical
  unfold exp3LossStep
  have hsingle :
      1 - exp3RewardIncrement η m h a (a, r) =
        (1 - r) / exp3Prob η m h a := by
    simp [exp3RewardIncrement]
  rw [← hsingle]
  apply Finset.sum_eq_single a
  · intro j hj hja
    simp [exp3RewardIncrement, Ne.symm hja]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

private lemma exp3LossStep_integrable_step {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (m : ℕ) (h : BanditHistory k m) :
    Integrable (exp3LossStep η m h) (adversarialStepKernel x π m h) := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  apply (integrable_map_measure
    (exp3LossStep_measurable η m h).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  exact Integrable.of_finite

private lemma exp3LossStep_norm_integral_le_card {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π)
    (m : ℕ) (h : BanditHistory k m) :
    (∫ z, ‖exp3LossStep η m h z‖ ∂(adversarialStepKernel x π m h)) ≤ k := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp3LossStep_measurable η m h).norm.aestronglyMeasurable]
  rw [hπ m h, integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ a : Fin k,
        (ENNReal.ofReal (exp3Prob η m h a)).toReal = exp3Prob η m h a :=
      fun a ↦ ENNReal.toReal_ofReal (exp3Prob_pos_adv η m h a).le
    simp_rw [htoReal, exp3LossStep_action]
    calc
      (∑ a, exp3Prob η m h a * ‖(1 - x m a) / exp3Prob η m h a‖) =
          ∑ a, (1 - x m a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Real.norm_eq_abs, abs_of_nonneg
          (div_nonneg (sub_nonneg.mpr (hx m a).2) (exp3Prob_pos_adv η m h a).le)]
        field_simp [(exp3Prob_pos_adv η m h a).ne']
      _ ≤ ∑ _a : Fin k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        linarith [(hx m a).1]
      _ = k := by simp
  · intro a ha
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp3LossStep_integrable_joint {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π) (m : ℕ) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      exp3LossStep η m p.1 p.2)
      ((adversarialMeasure x π m).compProd (adversarialStepKernel x π m)) := by
  apply (Measure.integrable_compProd_iff
    (exp3LossStep_joint_measurable η m).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      exp3LossStep_integrable_step x π η m h
  · apply Integrable.of_mem_Icc 0 k
    · exact (exp3LossStep_joint_measurable η m).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun z ↦ norm_nonneg _)
        · exact exp3LossStep_norm_integral_le_card x hx π η hπ m h

private lemma exp3LossMass_measurable {k : ℕ} (η : ℝ) :
    ∀ m : ℕ, Measurable (fun h : BanditHistory k m ↦ exp3LossMass η m h) := by
  intro m
  induction m with
  | zero => simp [exp3LossMass]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hpair : Measurable
          (fun h : BanditHistory k (m + 1) ↦ (Fin.init h, h (Fin.last m))) :=
        hinit.prodMk hlast
      simpa only [exp3LossMass, exp3LossStep, Pi.add_def, Function.comp_def] using
        (ih.comp hinit).add ((exp3LossStep_joint_measurable η m).comp hpair)

private theorem exp3LossMass_integrable_integral_le {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π) :
    ∀ m : ℕ,
      Integrable (fun h : BanditHistory k m ↦ exp3LossMass η m h)
          (adversarialMeasure x π m) ∧
        (∫ h, exp3LossMass η m h ∂(adversarialMeasure x π m)) ≤ m * k := by
  intro m
  induction m with
  | zero => simp [exp3LossMass, adversarialMeasure]
  | succ m ih =>
      let μ := adversarialMeasure x π m
      let κ := adversarialStepKernel x π m
      let snoc : BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc p.1 p.2
      have hsnoc : Measurable snoc := measurable_banditHistorySnoc
      have hrewrite :
          (fun p ↦ exp3LossMass η (m + 1) (snoc p)) =
            fun p ↦ exp3LossMass η m p.1 + exp3LossStep η m p.1 p.2 := by
        funext p
        simp [snoc, exp3LossMass_snoc, exp3LossStep]
      have hold : Integrable
          (fun p : BanditHistory k m × (Fin k × ℝ) ↦ exp3LossMass η m p.1)
          (μ.compProd κ) := by
        have hi : Integrable (fun h : BanditHistory k m ↦ exp3LossMass η m h)
            (Measure.map Prod.fst (μ.compProd κ)) := by
          change Integrable (fun h : BanditHistory k m ↦ exp3LossMass η m h)
            ((μ.compProd κ).fst)
          rw [Measure.fst_compProd]
          exact ih.1
        exact hi.comp_aemeasurable measurable_fst.aemeasurable
      have hnew : Integrable
          (fun p : BanditHistory k m × (Fin k × ℝ) ↦ exp3LossStep η m p.1 p.2)
          (μ.compProd κ) := exp3LossStep_integrable_joint x hx π η hπ m
      have hcomp : Integrable
          ((fun h : BanditHistory k (m + 1) ↦ exp3LossMass η (m + 1) h) ∘ snoc)
          (μ.compProd κ) := by
        change Integrable (fun p ↦ exp3LossMass η (m + 1) (snoc p)) (μ.compProd κ)
        rw [hrewrite]
        exact hold.add hnew
      constructor
      · rw [adversarialMeasure]
        apply (integrable_map_measure
          (exp3LossMass_measurable η (m + 1)).aestronglyMeasurable
          hsnoc.aemeasurable).2
        exact hcomp
      · rw [adversarialMeasure,
          integral_map hsnoc.aemeasurable
            (exp3LossMass_measurable η (m + 1)).aestronglyMeasurable]
        rw [hrewrite, integral_add hold hnew,
          Measure.integral_compProd hold, Measure.integral_compProd hnew]
        simp_rw [integral_const]
        have hkappa (h : BanditHistory k m) : (κ h).real Set.univ = 1 := by
          simp [κ]
        simp_rw [hkappa, one_smul]
        have hinner : Integrable
            (fun h : BanditHistory k m ↦
              ∫ z, exp3LossStep η m h z ∂(κ h)) μ := hnew.integral_compProd
        have hinner_le :
            (∫ h, (∫ z, exp3LossStep η m h z ∂(κ h)) ∂μ) ≤ k := by
          calc
            _ ≤ ∫ _h : BanditHistory k m, (k : ℝ) ∂μ := by
              apply integral_mono hinner (integrable_const _)
              intro h
              simpa [exp3LossStep, κ] using
                exp3_loss_sum_integral_step_le_card_adv x hx π η hπ m h
            _ = k := by simp
        change (∫ h, exp3LossMass η m h ∂μ) +
            (∫ h, (∫ z, exp3LossStep η m h z ∂(κ h)) ∂μ) ≤
              ((m + 1 : ℕ) : ℝ) * (k : ℝ)
        have hold_le : (∫ h, exp3LossMass η m h ∂μ) ≤ m * k := by
          simpa [μ] using ih.2
        norm_num at hold_le hinner_le ⊢
        nlinarith

end BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditAlgorithm.BanditPolicy k) (η : ℝ) (hη : 0 < η)
    (hπ : BanditAlgorithm.IsExp3Policy η π) (i : Fin k) :
    (∫ h, BanditAlgorithm.exp3Estimate η n h i
      ∂(BanditAlgorithm.adversarialMeasure x π n)) -
        (∫ h, (∑ t, (h t).2) ∂(BanditAlgorithm.adversarialMeasure x π n)) ≤
      Real.log k / η + η * n * k / 2 := by
  let μ := BanditAlgorithm.adversarialMeasure x π n
  have hest :=
    (BanditAlgorithm.exp3Estimate_integrable_integral_test x hx π η hπ n i).1
  have hreward := BanditAlgorithm.rewardSum_integrable x hx π n
  have hloss :=
    BanditAlgorithm.exp3LossMass_integrable_integral_le x hx π η hπ n
  have hloss_int : Integrable
      (fun h : BanditAlgorithm.BanditHistory k n ↦
        BanditAlgorithm.exp3LossMass η n h) μ := by
    simpa [μ] using hloss.1
  have hleft : Integrable
      (fun h : BanditAlgorithm.BanditHistory k n ↦
        BanditAlgorithm.exp3Estimate η n h i - ∑ t, (h t).2) μ :=
    hest.sub hreward
  have hright : Integrable
      (fun h : BanditAlgorithm.BanditHistory k n ↦
        Real.log k / η + (η / 2) * BanditAlgorithm.exp3LossMass η n h) μ :=
    (integrable_const _).add (hloss_int.const_mul (η / 2))
  have hmono :
      (∫ h, BanditAlgorithm.exp3Estimate η n h i ∂μ) -
          (∫ h, (∑ t, (h t).2) ∂μ) ≤
        Real.log k / η + (η / 2) *
          (∫ h, BanditAlgorithm.exp3LossMass η n h ∂μ) := by
    calc
      _ = ∫ h, (BanditAlgorithm.exp3Estimate η n h i - ∑ t, (h t).2) ∂μ :=
        (integral_sub hest hreward).symm
      _ ≤ ∫ h, (Real.log k / η +
          (η / 2) * BanditAlgorithm.exp3LossMass η n h) ∂μ := by
        apply integral_mono_ae hleft hright
        filter_upwards [BanditAlgorithm.adversarialMeasure_ae_good x hx π n] with h hh
        have hp := BanditAlgorithm.exp3_pathwise_advantage_bound hk η hη n h hh i
        nlinarith
      _ = _ := by
        rw [integral_add (integrable_const _) (hloss_int.const_mul (η / 2)),
          integral_const_mul]
        simp
  have hscale := mul_le_mul_of_nonneg_left hloss.2 (by positivity : 0 ≤ η / 2)
  change (∫ h, BanditAlgorithm.exp3Estimate η n h i ∂μ) -
      (∫ h, (∑ t, (h t).2) ∂μ) ≤ Real.log k / η + η * n * k / 2
  nlinarith
