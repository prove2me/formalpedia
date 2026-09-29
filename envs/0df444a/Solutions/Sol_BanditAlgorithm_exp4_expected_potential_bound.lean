-- Prove2me | solution 1 for BanditAlgorithm.exp4_expected_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T00:36:26.653144+00:00
-- url     : https://prove2.me/submissions/dae133c7-56a5-4759-ae5a-9136c012d777

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Direct proof of Lattimore--Szepesvári, *Bandit Algorithms*, Lemma 18.2
as used in Eq. (18.9), and its expected form in Eq. (18.11), printed p. 230.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private lemma exp_le_quadratic_of_nonpos_exp4 (x : ℝ) (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun y ↦ 1 + y + y ^ 2 / 2 - Real.exp y
  have hfderiv : ∀ y : ℝ, HasDerivAt f (1 + y - Real.exp y) y := by
    intro y
    dsimp [f]
    convert ((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
      ((hasDerivAt_id y).pow 2 |>.div_const 2)).sub
        (Real.hasDerivAt_exp y)) using 1 <;>
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

private lemma exp_scaled_le_shifted_quadratic_exp4
    (η y : ℝ) (hη : 0 ≤ η) (hy : y ≤ 1) :
    Real.exp (η * y) ≤
      Real.exp η *
        (1 + η * (y - 1) + (η ^ 2 / 2) * (y - 1) ^ 2) := by
  rw [show η * y = η + η * (y - 1) by ring, Real.exp_add]
  gcongr
  convert exp_le_quadratic_of_nonpos_exp4
    (η * (y - 1))
    (mul_nonpos_of_nonneg_of_nonpos hη (by linarith)) using 1 <;>
    first | rfl | ring

private lemma weighted_exp_sum_le_potential_exp4
    {M : ℕ} (q y : Fin M → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hq : ∀ m, 0 ≤ q m) (hsum : ∑ m, q m = 1)
    (hy : ∀ m, y m ≤ 1) :
    (∑ m, q m * Real.exp (η * y m)) ≤
      Real.exp (η * ∑ m, q m * y m +
        (η ^ 2 / 2) * ∑ m, q m * (y m - 1) ^ 2) := by
  classical
  have hshift : (∑ m, q m * (y m - 1)) =
      (∑ m, q m * y m) - 1 := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hsum]
  let z := η * (∑ m, q m * (y m - 1)) +
    (η ^ 2 / 2) * ∑ m, q m * (y m - 1) ^ 2
  calc
    (∑ m, q m * Real.exp (η * y m)) ≤
        Real.exp η * ∑ m, q m *
          (1 + η * (y m - 1) +
            (η ^ 2 / 2) * (y m - 1) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left
          (exp_scaled_le_shifted_quadratic_exp4
            η (y m) hη (hy m)) (hq m)
    _ = Real.exp η * (1 + z) := by
      dsimp [z]
      have hsum_expand :
          (∑ m, q m *
            (1 + η * (y m - 1) +
              (η ^ 2 / 2) * (y m - 1) ^ 2)) =
            (∑ m, q m) + η * (∑ m, q m * (y m - 1)) +
              (η ^ 2 / 2) * (∑ m, q m * (y m - 1) ^ 2) := by
        calc
          _ = ∑ m, (q m + η * (q m * (y m - 1)) +
              (η ^ 2 / 2) * (q m * (y m - 1) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ = (∑ m, q m) + (∑ m, η * (q m * (y m - 1))) +
              ∑ m, (η ^ 2 / 2) * (q m * (y m - 1) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
      rw [hsum_expand, hsum]
      ring
    _ ≤ Real.exp η * Real.exp z :=
      mul_le_mul_of_nonneg_left
        (by simpa [add_comm] using Real.add_one_le_exp z)
        (Real.exp_pos η).le
    _ = Real.exp (η * ∑ m, q m * y m +
        (η ^ 2 / 2) * ∑ m, q m * (y m - 1) ^ 2) := by
      rw [← Real.exp_add]
      dsimp [z]
      rw [hshift]
      ring

private lemma exp4Weights_pos_pot {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (m : Fin M) :
    0 < exp4ExpertWeights η 0 E r h m := by
  unfold exp4ExpertWeights expWeights
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨m, Finset.mem_univ _, Real.exp_pos _⟩

private lemma sum_exp4Weights_pot {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (m₀ : Fin M) :
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

private lemma exp4Prob_nonneg_pot {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (r : ℕ) (h : BanditHistory k r) (a : Fin k) :
    0 ≤ exp4Prob η 0 E r h a := by
  unfold exp4Prob
  exact Finset.sum_nonneg fun m _ ↦
    mul_nonneg (exp4Weights_pos_pot η E r h m).le (hE0 r m a)

private lemma exp4RewardIncrement_le_one_pot {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (r : ℕ) (h : BanditHistory k r) (m : Fin M)
    (z : Fin k × ℝ) (hz : z.2 ≤ 1) :
    exp4RewardIncrement η E r h m z ≤ 1 := by
  classical
  unfold exp4RewardIncrement
  calc
    (∑ a, E r m a *
        (1 - if z.1 = a then
          (1 - z.2) / exp4Prob η 0 E r h a
        else 0)) ≤
        ∑ a, E r m a := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_of_le_one_right (hE0 r m a)
      apply sub_le_self
      by_cases hza : z.1 = a
      · simp only [if_pos hza]
        exact div_nonneg (sub_nonneg.mpr hz)
          (exp4Prob_nonneg_pot η E hE0 r h a)
      · simp [hza]
    _ = 1 := hE1 r m

private lemma exp4Estimate_snoc_pot {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (z : Fin k × ℝ) (m : Fin M) :
    exp4Estimate η 0 E (r + 1) (Fin.snoc h z) m =
      exp4Estimate η 0 E r h m +
        exp4RewardIncrement η E r h m z := by
  simp [exp4Estimate, exp4RewardIncrement, exp4Prob,
    exp4ExpertWeights]

private noncomputable def exp4MixtureStep {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (z : Fin k × ℝ) : ℝ :=
  ∑ m, exp4ExpertWeights η 0 E r h m *
    exp4RewardIncrement η E r h m z

private noncomputable def exp4QuadraticStep {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (z : Fin k × ℝ) : ℝ :=
  ∑ m, exp4ExpertWeights η 0 E r h m *
    (1 - exp4RewardIncrement η E r h m z) ^ 2

private lemma expWeights_potential_ratio_pot
    {M : ℕ} (η : ℝ) (s y : Fin M → ℝ) :
    (∑ m, Real.exp (η * (s m + y m))) /
        (∑ m, Real.exp (η * s m)) =
      ∑ m, expWeights (fun j ↦ η * s j) m *
        Real.exp (η * y m) := by
  simp only [expWeights]
  rw [show
      (∑ m, Real.exp (η * s m) / (∑ j, Real.exp (η * s j)) *
        Real.exp (η * y m)) =
      (∑ m, Real.exp (η * s m) * Real.exp (η * y m)) /
        (∑ j, Real.exp (η * s j)) by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    ring]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Real.exp_add]
  congr 1
  ring

private lemma exp4_potential_ratio_pot {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (z : Fin k × ℝ) :
    (∑ m, Real.exp
        (η * exp4Estimate η 0 E (r + 1) (Fin.snoc h z) m)) /
        (∑ m, Real.exp (η * exp4Estimate η 0 E r h m)) =
      ∑ m, exp4ExpertWeights η 0 E r h m *
        Real.exp (η * exp4RewardIncrement η E r h m z) := by
  simp_rw [exp4Estimate_snoc_pot]
  simpa only [exp4ExpertWeights] using
    expWeights_potential_ratio_pot η
      (fun m ↦ exp4Estimate η 0 E r h m)
      (fun m ↦ exp4RewardIncrement η E r h m z)

private lemma exp4_one_step_potential_pot {k M : ℕ} (η : ℝ)
    (hη : 0 ≤ η) (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (r : ℕ) (h : BanditHistory k r) (z : Fin k × ℝ)
    (hz : z.2 ≤ 1) (m₀ : Fin M) :
    (∑ m, Real.exp
        (η * exp4Estimate η 0 E (r + 1) (Fin.snoc h z) m)) /
        (∑ m, Real.exp (η * exp4Estimate η 0 E r h m)) ≤
      Real.exp
        (η * exp4MixtureStep η E r h z +
          (η ^ 2 / 2) * exp4QuadraticStep η E r h z) := by
  rw [exp4_potential_ratio_pot]
  have hw := weighted_exp_sum_le_potential_exp4
    (fun m ↦ exp4ExpertWeights η 0 E r h m)
    (fun m ↦ exp4RewardIncrement η E r h m z)
    η hη
    (fun m ↦ (exp4Weights_pos_pot η E r h m).le)
    (sum_exp4Weights_pot η E r h m₀)
    (fun m ↦ exp4RewardIncrement_le_one_pot
      η E hE0 hE1 r h m z hz)
  convert hw using 1 <;>
    simp only [exp4MixtureStep, exp4QuadraticStep] <;>
    ring

private noncomputable def exp4Potential {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) : ℝ :=
  ∑ m, Real.exp (η * exp4Estimate η 0 E r h m)

private lemma exp4Potential_pos {k M : ℕ} (hM : 0 < M) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) :
    0 < exp4Potential η E r h := by
  unfold exp4Potential
  exact Finset.sum_pos' (fun m _ ↦ (Real.exp_pos _).le)
    ⟨Classical.choice (Fin.pos_iff_nonempty.mp hM),
      Finset.mem_univ _, Real.exp_pos _⟩

private lemma exp4_comparator_exp_le_potential {k M r : ℕ}
    (η : ℝ) (E : ℕ → Fin M → Fin k → ℝ)
    (h : BanditHistory k r) (m : Fin M) :
    Real.exp (η * exp4Estimate η 0 E r h m) ≤
      exp4Potential η E r h := by
  unfold exp4Potential
  exact Finset.single_le_sum
    (fun j _ ↦ (Real.exp_pos
      (η * exp4Estimate η 0 E r h j)).le)
    (Finset.mem_univ m)

private lemma exp4_log_potential_bound {k M : ℕ} (hM : 0 < M)
    (η : ℝ) (hη : 0 ≤ η)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (m₀ : Fin M) :
    ∀ (r : ℕ) (h : BanditHistory k r),
      (∀ t : Fin r, (h t).2 ∈ Set.Icc (0 : ℝ) 1) →
      Real.log (exp4Potential η E r h) ≤
        Real.log M + η * exp4MixtureEstimate η E r h +
          (η ^ 2 / 2) * exp4QuadraticMass η E r h := by
  intro r
  induction r with
  | zero =>
      intro h hh
      simp [exp4Potential, exp4Estimate, exp4MixtureEstimate,
        exp4QuadraticMass]
  | succ r ih =>
      intro h hh
      let h0 : BanditHistory k r := Fin.init h
      let z : Fin k × ℝ := h (Fin.last r)
      have hh0 : ∀ t : Fin r, (h0 t).2 ∈ Set.Icc (0 : ℝ) 1 := by
        intro t
        exact hh (Fin.castSucc t)
      have hz : z.2 ∈ Set.Icc (0 : ℝ) 1 := hh (Fin.last r)
      have hstep :=
        exp4_one_step_potential_pot
          η hη E hE0 hE1 r h0 z hz.2 m₀
      have hratio :
          exp4Potential η E (r + 1) h / exp4Potential η E r h0 ≤
            Real.exp
              (η * exp4MixtureStep η E r h0 z +
                (η ^ 2 / 2) * exp4QuadraticStep η E r h0 z) := by
        simpa [exp4Potential, h0, z] using hstep
      have hnewpos : 0 < exp4Potential η E (r + 1) h :=
        exp4Potential_pos hM η E _ h
      have holdpos : 0 < exp4Potential η E r h0 :=
        exp4Potential_pos hM η E _ h0
      have hlogstep :
          Real.log (exp4Potential η E (r + 1) h) ≤
            Real.log (exp4Potential η E r h0) +
              (η * exp4MixtureStep η E r h0 z +
                (η ^ 2 / 2) * exp4QuadraticStep η E r h0 z) := by
        have hlogratio :
            Real.log
              (exp4Potential η E (r + 1) h /
                exp4Potential η E r h0) ≤
              η * exp4MixtureStep η E r h0 z +
                (η ^ 2 / 2) * exp4QuadraticStep η E r h0 z :=
          (Real.log_le_iff_le_exp (div_pos hnewpos holdpos)).2 hratio
        rw [Real.log_div hnewpos.ne' holdpos.ne'] at hlogratio
        linarith
      have hi := ih h0 hh0
      have hsnoc : h = Fin.snoc h0 z := by simp [h0, z]
      rw [hsnoc]
      simp only [exp4MixtureEstimate, exp4QuadraticMass,
        Fin.init_snoc, Fin.snoc_last]
      change
        Real.log (exp4Potential η E (r + 1) (Fin.snoc h0 z)) ≤
          Real.log M +
            η * (exp4MixtureEstimate η E r h0 +
              exp4MixtureStep η E r h0 z) +
            (η ^ 2 / 2) *
              (exp4QuadraticMass η E r h0 +
                exp4QuadraticStep η E r h0 z)
      calc
        Real.log (exp4Potential η E (r + 1) (Fin.snoc h0 z)) ≤
            Real.log (exp4Potential η E r h0) +
              (η * exp4MixtureStep η E r h0 z +
                (η ^ 2 / 2) * exp4QuadraticStep η E r h0 z) := by
          simpa [hsnoc] using hlogstep
        _ ≤ (Real.log M + η * exp4MixtureEstimate η E r h0 +
              (η ^ 2 / 2) * exp4QuadraticMass η E r h0) +
              (η * exp4MixtureStep η E r h0 z +
                (η ^ 2 / 2) * exp4QuadraticStep η E r h0 z) := by
          linarith
        _ = _ := by ring

private lemma exp4_pathwise_potential_bound {k M : ℕ} (hM : 0 < M)
    (η : ℝ) (hη : 0 < η)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (m₀ : Fin M) (r : ℕ) (h : BanditHistory k r)
    (hh : ∀ t : Fin r, (h t).2 ∈ Set.Icc (0 : ℝ) 1)
    (m : Fin M) :
    exp4Estimate η 0 E r h m - exp4MixtureEstimate η E r h ≤
      Real.log M / η + (η / 2) * exp4QuadraticMass η E r h := by
  have hcomp :
      η * exp4Estimate η 0 E r h m ≤
        Real.log (exp4Potential η E r h) := by
    apply (Real.le_log_iff_exp_le
      (exp4Potential_pos hM η E r h)).2
    exact exp4_comparator_exp_le_potential η E h m
  have hpot :=
    exp4_log_potential_bound hM η hη.le E hE0 hE1 m₀ r h hh
  have hmain :
      η * (exp4Estimate η 0 E r h m -
        exp4MixtureEstimate η E r h) ≤
        Real.log M +
          (η ^ 2 / 2) * exp4QuadraticMass η E r h := by
    nlinarith
  calc
    exp4Estimate η 0 E r h m - exp4MixtureEstimate η E r h ≤
        (Real.log M +
          (η ^ 2 / 2) * exp4QuadraticMass η E r h) / η :=
      (le_div_iff₀ hη).2 (by simpa [mul_comm] using hmain)
    _ = Real.log M / η +
        (η / 2) * exp4QuadraticMass η E r h := by
      field_simp [hη.ne']

private lemma exp4Estimate_measurable_pot {k M : ℕ} (η : ℝ)
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

private lemma exp4Prob_measurable_pot {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (a : Fin k) :
    Measurable (fun h : BanditHistory k r ↦ exp4Prob η 0 E r h a) := by
  unfold exp4Prob exp4ExpertWeights expWeights
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.mul
  · apply Measurable.div
    · exact Real.continuous_exp.measurable.comp
        (measurable_const.mul (exp4Estimate_measurable_pot η E r m))
    · apply Finset.measurable_sum
      intro j hj
      exact Real.continuous_exp.measurable.comp
        (measurable_const.mul (exp4Estimate_measurable_pot η E r j))
  · exact measurable_const

private lemma exp4RewardIncrement_joint_measurable_pot {k M : ℕ} (η : ℝ)
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
      ((exp4Prob_measurable_pot η E r a).comp measurable_fst)
  exact Measurable.ite hcond hfrac measurable_const

private lemma exp4MixtureStep_joint_measurable_pot {k M : ℕ} (η : ℝ)
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
          ((exp4Estimate_measurable_pot η E r m).comp measurable_fst))
    · apply Finset.measurable_sum
      intro j hj
      exact Real.continuous_exp.measurable.comp
        (measurable_const.mul
          ((exp4Estimate_measurable_pot η E r j).comp measurable_fst))
  · exact exp4RewardIncrement_joint_measurable_pot η E r m

private lemma exp4QuadraticStep_joint_measurable_pot {k M : ℕ} (η : ℝ)
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
          ((exp4Estimate_measurable_pot η E r m).comp measurable_fst))
    · apply Finset.measurable_sum
      intro j hj
      exact Real.continuous_exp.measurable.comp
        (measurable_const.mul
          ((exp4Estimate_measurable_pot η E r j).comp measurable_fst))
  · exact (measurable_const.sub
      (exp4RewardIncrement_joint_measurable_pot η E r m)).pow_const 2

private lemma exp4MixtureEstimate_measurable_pot {k M : ℕ} (η : ℝ)
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
          ((exp4MixtureStep_joint_measurable_pot η E r).comp hpair)

private lemma exp4QuadraticMass_measurable_pot {k M : ℕ} (η : ℝ)
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
          ((exp4QuadraticStep_joint_measurable_pot η E r).comp hpair)

private theorem integrable_adversarial_of_measurable_pot {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) :
    ∀ (r : ℕ) (f : BanditHistory k r → ℝ),
      Measurable f → Integrable f (adversarialMeasure x π r) := by
  intro r
  induction r with
  | zero =>
      intro f hf
      rw [adversarialMeasure]
      exact integrable_dirac (by simp)
  | succ r ih =>
      intro f hf
      let μ := adversarialMeasure x π r
      let κ := adversarialStepKernel x π r
      let snoc : BanditHistory k r × (Fin k × ℝ) →
          BanditHistory k (r + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      have hsnoc : Measurable snoc := measurable_banditHistorySnoc
      have hg : Measurable (f ∘ snoc) := hf.comp hsnoc
      rw [adversarialMeasure]
      apply (integrable_map_measure
        hf.aestronglyMeasurable hsnoc.aemeasurable).2
      apply (Measure.integrable_compProd_iff hg.aestronglyMeasurable).2
      constructor
      · exact Filter.Eventually.of_forall fun h ↦ by
          rw [adversarialStepKernel,
            Kernel.map_apply _ (measurable_of_countable _) h]
          have hgz : Measurable
              (fun z : Fin k × ℝ ↦ (f ∘ snoc) (h, z)) :=
            hg.comp (measurable_const.prodMk measurable_id)
          apply (integrable_map_measure
            hgz.aestronglyMeasurable
            (measurable_of_countable _).aemeasurable).2
          exact Integrable.of_finite
      · have hinner :
            StronglyMeasurable (fun h : BanditHistory k r ↦
              ∫ z, ‖(f ∘ snoc) (h, z)‖ ∂(κ h)) :=
          hg.norm.stronglyMeasurable.integral_kernel_prod_right'
        exact ih _ hinner.measurable

private def GoodAdversarialHistoryPot {k r : ℕ}
    (h : BanditHistory k r) : Prop :=
  ∀ t : Fin r, (h t).2 ∈ Set.Icc (0 : ℝ) 1

private lemma measurableSet_goodAdversarialHistory_pot {k r : ℕ} :
    MeasurableSet {h : BanditHistory k r |
      GoodAdversarialHistoryPot h} := by
  rw [show
      {h : BanditHistory k r | GoodAdversarialHistoryPot h} =
        ⋂ t : Fin r,
          (fun h : BanditHistory k r ↦ (h t).2) ⁻¹' Set.Icc (0 : ℝ) 1 by
    ext h
    simp only [GoodAdversarialHistoryPot, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_preimage]]
  exact MeasurableSet.iInter fun t ↦
    measurableSet_Icc.preimage
      (measurable_snd.comp (measurable_pi_apply t))

private lemma adversarialMeasure_ae_good_pot {k : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) :
    ∀ r : ℕ, ∀ᵐ h ∂(adversarialMeasure x π r),
      GoodAdversarialHistoryPot h := by
  intro r
  induction r with
  | zero =>
      exact Filter.Eventually.of_forall fun h t ↦ t.elim0
  | succ r ih =>
      rw [adversarialMeasure]
      apply (ae_map_iff measurable_banditHistorySnoc.aemeasurable
        measurableSet_goodAdversarialHistory_pot).2
      apply Measure.ae_compProd_of_ae_ae
        (measurableSet_goodAdversarialHistory_pot.preimage
          measurable_banditHistorySnoc)
      filter_upwards [ih] with h hh
      rw [adversarialStepKernel,
        Kernel.map_apply _ (measurable_of_countable _) h]
      apply (ae_map_iff (measurable_of_countable _).aemeasurable
        (measurableSet_goodAdversarialHistory_pot.preimage
          (measurable_banditHistorySnoc.comp
            (measurable_const.prodMk measurable_id)))).2
      exact Filter.Eventually.of_forall fun a t ↦ by
        refine Fin.lastCases ?_ (fun s ↦ ?_) t
        · simpa using hx r a
        · simpa using hh s

end BanditAlgorithm

theorem solution
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp4Policy η 0 E π)
    (m : Fin M) :
    (∫ h, BanditAlgorithm.exp4Estimate η 0 E n h m
        ∂(BanditAlgorithm.adversarialMeasure x π n)) -
        (∫ h, BanditAlgorithm.exp4MixtureEstimate η E n h
          ∂(BanditAlgorithm.adversarialMeasure x π n)) ≤
      Real.log M / η +
        (η / 2) *
          (∫ h, BanditAlgorithm.exp4QuadraticMass η E n h
            ∂(BanditAlgorithm.adversarialMeasure x π n)) := by
  let μ := BanditAlgorithm.adversarialMeasure x π n
  let m₀ : Fin M := ⟨0, by omega⟩
  have hest : Integrable
      (fun h : BanditAlgorithm.BanditHistory k n ↦
        BanditAlgorithm.exp4Estimate η 0 E n h m) μ := by
    exact BanditAlgorithm.integrable_adversarial_of_measurable_pot
      x π n _ (BanditAlgorithm.exp4Estimate_measurable_pot η E n m)
  have hmix : Integrable
      (fun h : BanditAlgorithm.BanditHistory k n ↦
        BanditAlgorithm.exp4MixtureEstimate η E n h) μ := by
    exact BanditAlgorithm.integrable_adversarial_of_measurable_pot
      x π n _ (BanditAlgorithm.exp4MixtureEstimate_measurable_pot η E n)
  have hquad : Integrable
      (fun h : BanditAlgorithm.BanditHistory k n ↦
        BanditAlgorithm.exp4QuadraticMass η E n h) μ := by
    exact BanditAlgorithm.integrable_adversarial_of_measurable_pot
      x π n _ (BanditAlgorithm.exp4QuadraticMass_measurable_pot η E n)
  have hleft : Integrable
      (fun h : BanditAlgorithm.BanditHistory k n ↦
        BanditAlgorithm.exp4Estimate η 0 E n h m -
          BanditAlgorithm.exp4MixtureEstimate η E n h) μ :=
    hest.sub hmix
  have hright : Integrable
      (fun h : BanditAlgorithm.BanditHistory k n ↦
        Real.log M / η +
          (η / 2) * BanditAlgorithm.exp4QuadraticMass η E n h) μ :=
    (integrable_const _).add (hquad.const_mul (η / 2))
  calc
    (∫ h, BanditAlgorithm.exp4Estimate η 0 E n h m ∂μ) -
        (∫ h, BanditAlgorithm.exp4MixtureEstimate η E n h ∂μ) =
        ∫ h, (BanditAlgorithm.exp4Estimate η 0 E n h m -
          BanditAlgorithm.exp4MixtureEstimate η E n h) ∂μ :=
      (integral_sub hest hmix).symm
    _ ≤ ∫ h, (Real.log M / η +
        (η / 2) * BanditAlgorithm.exp4QuadraticMass η E n h) ∂μ := by
      apply integral_mono_ae hleft hright
      filter_upwards
        [BanditAlgorithm.adversarialMeasure_ae_good_pot x hx π n]
          with h hh
      exact BanditAlgorithm.exp4_pathwise_potential_bound
        (by omega) η hη E hE0 hE1 m₀ n h hh m
    _ = Real.log M / η +
        (η / 2) *
          (∫ h, BanditAlgorithm.exp4QuadraticMass η E n h ∂μ) := by
      rw [integral_add (integrable_const _)
        (hquad.const_mul (η / 2)), integral_const_mul]
      simp
