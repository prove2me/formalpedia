-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_expected_regret_known_reward_diam_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T16:21:30.322429+00:00
-- url     : https://prove2.me/submissions/b2eba635-7088-4019-8add-8315e4f82a67

import Definitions.Def_FiniteMDPLearning
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.ExponentialBounds
import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_high_probability_regret_known_reward_diam_ge_one

/-!
Reduction of the expected-regret bound (L&S Eq. (38.12), printed p. 523) to the
high-probability bound (Theorem 38.6), as indicated in Exercise 38.18.

Run the high-probability bound at confidence `δ = 1/n`. On the good event the regret is below
the threshold; on the bad event, of probability at most `1/n`, it is at most the horizon `n`,
contributing at most `n · (1/n) = 1` — which is exactly the additive `1` in the statement.

The resulting logarithm is `log(n²SA)` rather than `log n`, so the two regimes are separated:
when `SA ≤ n²` one has `log(n²SA) ≤ 4 log n` and the constant absorbs the difference; when
`SA > n²` the claimed bound already exceeds the horizon `n` and the trivial regret ceiling
finishes the job.
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

variable {S A : ℕ}

/-- A constant policy, used only to witness that policies exist. -/
private noncomputable def constPolicy (a : Fin A) : MDPPolicy S A where
  select _ := Kernel.const _ (Measure.dirac a)
  markov _ := by infer_instance

private lemma reward_nonneg {n : ℕ} (M : FiniteMDP S A)
    (hr : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1) (h : MDPTrajectory S A n) :
    0 ≤ mdpTrajectoryReward M h :=
  Finset.sum_nonneg fun t _ ↦ (hr _ _).1

private lemma reward_le {n : ℕ} (M : FiniteMDP S A)
    (hr : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1) (h : MDPTrajectory S A n) :
    mdpTrajectoryReward M h ≤ n := by
  calc mdpTrajectoryReward M h ≤ ∑ _t : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ ↦ (hr _ _).2
    _ = n := by simp

private lemma expectedReward_le {n : ℕ} (M : FiniteMDP S A)
    (hr : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) : mdpExpectedReward M μ0 π n ≤ n := by
  rw [mdpExpectedReward]
  calc ∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M μ0 π n)
      ≤ ∫ _h, (n : ℝ) ∂(mdpMeasure M μ0 π n) :=
        integral_mono (Integrable.of_finite) (Integrable.of_finite)
          (fun h ↦ reward_le M hr h)
    _ = n := by simp

private lemma expectedReward_nonneg {n : ℕ} (M : FiniteMDP S A)
    (hr : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) : 0 ≤ mdpExpectedReward M μ0 π n :=
  integral_nonneg fun h ↦ reward_nonneg M hr h

private lemma optimalGain_le_one (hS : 0 < S) (hA : 0 < A) (M : FiniteMDP S A)
    (hr : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1) : mdpOptimalGain M ≤ 1 := by
  haveI : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  haveI : Nonempty (MDPPolicy S A) := ⟨constPolicy ⟨0, hA⟩⟩
  refine ciSup_le fun s ↦ ciSup_le fun π ↦ ?_
  refine Filter.limsup_le_of_le ?_ (Filter.Eventually.of_forall fun m ↦ ?_)
  · refine ⟨0, fun a ha ↦ ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨m, hm⟩ := ha.exists
    exact le_trans (div_nonneg (expectedReward_nonneg M hr _ π) (Nat.cast_nonneg m)) hm
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · rw [div_le_one (by exact_mod_cast hm)]
      exact expectedReward_le M hr _ π

private lemma regret_le_horizon (hS : 0 < S) (hA : 0 < A) {n : ℕ} (M : FiniteMDP S A)
    (hr : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1) (h : MDPTrajectory S A n) :
    mdpRegret M n h ≤ n := by
  have h1 : (n : ℝ) * mdpOptimalGain M ≤ n := by
    nlinarith [optimalGain_le_one hS hA M hr, Nat.cast_nonneg (α := ℝ) n]
  have h2 : 0 ≤ mdpTrajectoryReward M h := reward_nonneg M hr h
  rw [mdpRegret]
  linarith

/-- Expected regret is at most the horizon. -/
private lemma integral_regret_le_horizon (hS : 0 < S) (hA : 0 < A) {n : ℕ} (M : FiniteMDP S A)
    (hr : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) : ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) ≤ n := by
  calc ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n)
      ≤ ∫ _h, (n : ℝ) ∂(mdpMeasure M μ0 π n) :=
        integral_mono Integrable.of_finite Integrable.of_finite
          (fun h ↦ regret_le_horizon hS hA M hr h)
    _ = n := by simp

theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
        ∀ r : Fin S → Fin A → ℝ, (∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) →
          ∃ π : MDPPolicy S A,
            ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating →
              1 ≤ mdpDiameter M →
              ∀ μ0 : MDPStateDistribution S,
                ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) ≤
                  1 + C * mdpDiameter M * S *
                    Real.sqrt (2 * A * n * Real.log n) := by
  classical
  obtain ⟨C, hC, hchild⟩ :=
    BanditAlgorithm.mdp_ucrl2_high_probability_regret_known_reward_diam_ge_one
  refine ⟨max (C * Real.sqrt 2) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro S A n hS hA hn r hr
  set C' : ℝ := max (C * Real.sqrt 2) 1 with hC'def
  have hC'1 : (1 : ℝ) ≤ C' := le_max_right _ _
  have hC'2 : C * Real.sqrt 2 ≤ C' := le_max_left _ _
  by_cases hn1 : n = 1
  · -- horizon one: the right-hand side is exactly `1`, and the regret never exceeds the horizon
    refine ⟨constPolicy ⟨0, hA⟩, fun M hMr _ hD μ0 ↦ ?_⟩
    have hrM : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1 := by rw [hMr]; exact hr
    subst hn1
    have h1 := integral_regret_le_horizon (n := 1) hS hA M hrM μ0 (constPolicy ⟨0, hA⟩)
    have h2 : Real.sqrt (2 * A * (1 : ℕ) * Real.log (1 : ℕ)) = 0 := by
      norm_num
    rw [h2]
    simpa using h1
  · -- horizon at least two: run the high-probability bound at `δ = 1/n`
    have hn2 : 2 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hnpos : (0 : ℝ) < n := by linarith
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hδ : (1 / (n : ℝ)) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_lt_one hnpos]; linarith
    obtain ⟨π, hπ⟩ := hchild S A n hS hA hn (1 / (n : ℝ)) hδ r hr
    refine ⟨π, fun M hMr hcomm hD μ0 ↦ ?_⟩
    have hrM : ∀ s a, M.r s a ∈ Set.Icc (0 : ℝ) 1 := by rw [hMr]; exact hr
    have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hD0 : (0 : ℝ) < mdpDiameter M := by linarith
    set D := mdpDiameter M with hDdef
    set x := Real.sqrt ((A : ℝ) * n * Real.log n) with hxdef
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    -- the target's square root, factored
    have hsplit : Real.sqrt (2 * A * n * Real.log n) = Real.sqrt 2 * x := by
      rw [hxdef, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      ring_nf
    by_cases hcase : (S : ℝ) * A ≤ (n : ℝ) ^ 2
    · -- regime one: the logarithm is comparable to `log n`
      set T := C * D * S * Real.sqrt ((A : ℝ) * n * Real.log ((n : ℝ) * S * A / (1 / n))) with hTdef
      have hT0 : 0 ≤ T := by positivity
      have hbad := hπ M hMr hcomm hD μ0
      -- pointwise: regret ≤ T + n * 1_{regret ≥ T}
      have hmeas : MeasurableSet {h : MDPTrajectory S A n | T ≤ mdpRegret M n h} :=
        MeasurableSet.of_discrete
      have hpt : ∀ h, mdpRegret M n h ≤
          T + (n : ℝ) * Set.indicator {h : MDPTrajectory S A n | T ≤ mdpRegret M n h}
            (fun _ ↦ (1 : ℝ)) h := by
        intro h
        by_cases hh : T ≤ mdpRegret M n h
        · rw [Set.indicator_of_mem (show h ∈ {h : MDPTrajectory S A n | T ≤ mdpRegret M n h} from hh)]
          have := regret_le_horizon hS hA M hrM h
          simp only [mul_one]
          linarith
        · rw [Set.indicator_of_notMem (show h ∉ {h : MDPTrajectory S A n | T ≤ mdpRegret M n h} from hh)]
          push_neg at hh
          simp only [mul_zero, add_zero]
          linarith
      have hint : ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) ≤ T + 1 := by
        have hstep : ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) ≤
            ∫ h, (T + (n : ℝ) * Set.indicator {h : MDPTrajectory S A n | T ≤ mdpRegret M n h}
              (fun _ ↦ (1 : ℝ)) h) ∂(mdpMeasure M μ0 π n) :=
          integral_mono Integrable.of_finite Integrable.of_finite hpt
        have hev : ∫ h, (T + (n : ℝ) * Set.indicator
            {h : MDPTrajectory S A n | T ≤ mdpRegret M n h} (fun _ ↦ (1 : ℝ)) h)
            ∂(mdpMeasure M μ0 π n)
            = T + (n : ℝ) * (mdpMeasure M μ0 π n).real
              {h : MDPTrajectory S A n | T ≤ mdpRegret M n h} := by
          rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const,
            integral_const_mul, integral_indicator_const (1 : ℝ) hmeas]
          simp
        have hprob : (mdpMeasure M μ0 π n).real
            {h : MDPTrajectory S A n | T ≤ mdpRegret M n h} ≤ 1 / n := by
          have := ENNReal.toReal_mono (by simp) hbad
          rwa [ENNReal.toReal_ofReal (by positivity)] at this
        rw [hev] at hstep
        refine hstep.trans ?_
        have : (n : ℝ) * ((mdpMeasure M μ0 π n).real
            {h : MDPTrajectory S A n | T ≤ mdpRegret M n h}) ≤ (n : ℝ) * (1 / n) :=
          mul_le_mul_of_nonneg_left hprob (le_of_lt hnpos)
        rw [mul_one_div, div_self (ne_of_gt hnpos)] at this
        linarith
      -- and `T` is dominated by the target
      have hlog : Real.log ((n : ℝ) * S * A / (1 / n)) ≤ 4 * Real.log n := by
        have harg : (n : ℝ) * S * A / (1 / n) = (n : ℝ) * S * A * n := by
          field_simp
        rw [harg]
        have hle : (n : ℝ) * S * A * n ≤ (n : ℝ) ^ 4 := by
          have he : (n : ℝ) * S * A * n = (n : ℝ) ^ 2 * ((S : ℝ) * A) := by ring
          have h2 : (n : ℝ) ^ 2 * ((S : ℝ) * A) ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hcase (by positivity)
          calc (n : ℝ) * S * A * n = (n : ℝ) ^ 2 * ((S : ℝ) * A) := he
            _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := h2
            _ = (n : ℝ) ^ 4 := by ring
        have h1 : (0 : ℝ) < (n : ℝ) * S * A * n := by positivity
        calc Real.log ((n : ℝ) * S * A * n) ≤ Real.log ((n : ℝ) ^ 4) :=
              Real.log_le_log h1 hle
          _ = 4 * Real.log n := by rw [Real.log_pow]; norm_num
      have hTle : T ≤ C' * D * S * Real.sqrt (2 * A * n * Real.log n) := by
        have hsq : Real.sqrt ((A : ℝ) * n * Real.log ((n : ℝ) * S * A / (1 / n))) ≤ 2 * x := by
          have h4 : (A : ℝ) * n * Real.log ((n : ℝ) * S * A / (1 / n))
              ≤ 4 * ((A : ℝ) * n * Real.log n) := by
            have hAn : (0 : ℝ) ≤ (A : ℝ) * n := by positivity
            nlinarith [hlog, hAn]
          calc Real.sqrt ((A : ℝ) * n * Real.log ((n : ℝ) * S * A / (1 / n)))
              ≤ Real.sqrt (4 * ((A : ℝ) * n * Real.log n)) := Real.sqrt_le_sqrt h4
            _ = 2 * x := by
                have hs4 : Real.sqrt 4 = 2 := by
                  rw [show (4:ℝ) = 2 ^ 2 by norm_num,
                    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
                rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hs4, hxdef]
        rw [hsplit, hTdef]
        have hCS : 0 ≤ C * D * S := by positivity
        have hstep1 : C * D * S * Real.sqrt ((A : ℝ) * n * Real.log ((n:ℝ) * S * A / (1 / n)))
            ≤ C * D * S * (2 * x) := mul_le_mul_of_nonneg_left hsq hCS
        refine hstep1.trans ?_
        have h2 : C * (2 : ℝ) ≤ C' * Real.sqrt 2 := by
          have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          nlinarith [Real.sqrt_nonneg 2, hC'2, hC.le]
        nlinarith [hx0, hD0.le, hSR, mul_nonneg (mul_nonneg hD0.le (by linarith : (0:ℝ) ≤ (S:ℝ))) hx0]
      linarith
    · -- regime two: the claimed bound already exceeds the horizon
      push_neg at hcase
      have hbig : (n : ℝ) ≤ S * Real.sqrt (2 * A * n * Real.log n) := by
        have hSA : (n : ℝ) < S * Real.sqrt (A : ℝ) := by
          have h2 : ((S : ℝ) * Real.sqrt A) ^ 2 = (S : ℝ) ^ 2 * A := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
          have h3 : (n : ℝ) ^ 2 < ((S : ℝ) * Real.sqrt A) ^ 2 := by
            rw [h2]
            nlinarith [hcase, hSR, hAR]
          refine lt_of_pow_lt_pow_left₀ 2 (by positivity) h3
        have hroot : (1 : ℝ) ≤ Real.sqrt (2 * n * Real.log n) := by
          have : (1 : ℝ) ≤ 2 * n * Real.log n := by
            have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
            nlinarith [Real.log_two_gt_d9, hnR, this]
          simpa using Real.one_le_sqrt.mpr this
        have hfac : Real.sqrt (2 * A * n * Real.log n)
            = Real.sqrt (A : ℝ) * Real.sqrt (2 * n * Real.log n) := by
          rw [← Real.sqrt_mul (by positivity)]
          ring_nf
        rw [hfac]
        calc (n : ℝ) ≤ S * Real.sqrt (A : ℝ) := hSA.le
          _ = S * Real.sqrt (A : ℝ) * 1 := by ring
          _ ≤ S * Real.sqrt (A : ℝ) * Real.sqrt (2 * n * Real.log n) := by
              refine mul_le_mul_of_nonneg_left hroot ?_
              positivity
          _ = S * (Real.sqrt (A : ℝ) * Real.sqrt (2 * n * Real.log n)) := by ring
      have hle := integral_regret_le_horizon (n := n) hS hA M hrM μ0 π
      have hpos : 0 ≤ Real.sqrt (2 * A * n * Real.log n) := Real.sqrt_nonneg _
      have hSsq : 0 ≤ (S : ℝ) * Real.sqrt (2 * A * n * Real.log n) := by positivity
      have hcd : (1 : ℝ) ≤ C' * D := by nlinarith [hC'1, hD]
      have hgrow : (S : ℝ) * Real.sqrt (2 * A * n * Real.log n)
          ≤ C' * D * ((S : ℝ) * Real.sqrt (2 * A * n * Real.log n)) :=
        le_mul_of_one_le_left hSsq hcd
      have hassoc : C' * D * ((S : ℝ) * Real.sqrt (2 * A * n * Real.log n))
          = C' * D * S * Real.sqrt (2 * A * n * Real.log n) := by ring
      rw [hassoc] at hgrow
      linarith [hle, hbig, hgrow]

end BanditAlgorithm
