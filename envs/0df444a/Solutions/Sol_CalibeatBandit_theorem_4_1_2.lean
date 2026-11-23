-- Prove2me | solution 2 for CalibeatBandit.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:43:08.758805+00:00
-- url     : https://prove2.me/submissions/3d2db172-6948-4f21-8c4c-1c07415100fd

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Theorems.Thm_CalibeatBandit_exists_hard_tree_environment
import Theorems.Thm_CalibeatBandit_tree_scale_threshold

section

set_option autoImplicit false

namespace CalibeatBandit

open Set MeasureTheory

theorem feedbackHistory_eq_of_prior_rewards_eq {A : Type*}
    (pick : (t : ℕ) → FeedbackHistory t → A) (y y' : ℕ → A → ℝ) (t : ℕ)
    (h : ∀ s < t, ∀ a, y s a = y' s a) :
    feedbackHistory pick y t = feedbackHistory pick y' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
    simp only [feedbackHistory, he, h t (Nat.lt_succ_self t)]
    rfl

theorem card_treeNode (h : ℕ) : Fintype.card (TreeNode h) = 2 ^ (h + 1) - 1 := by
  simp only [TreeNode, Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  induction h with
  | zero => norm_num
  | succ h ih =>
    rw [Finset.sum_range_succ, ih, pow_succ (2 : ℕ) (h + 1)]
    have hp : 0 < (2 : ℕ) ^ (h + 1) := by positivity
    omega

/-- Choose the largest power-of-two leaf count that fits the action budget.
The remaining actions are unnamed and have zero bonus probability. -/
theorem exists_treeAction_equiv (N : ℕ) (hN : 32 ≤ N) :
    ∃ h U : ℕ, 0 < h ∧ 16 * 2 ^ h ≤ N ∧ N < 32 * 2 ^ h ∧
      Nonempty (Fin N ≃ TreeAction h (8 * 2 ^ h) U) := by
  let h := Nat.log 2 (N / 16)
  have hq : 2 ≤ N / 16 := by omega
  have hh : 0 < h := by
    have hh' := (Nat.le_log_iff_pow_le (by decide : 1 < 2)
      (show N / 16 ≠ 0 by omega)).2 (show 2 ^ 1 ≤ N / 16 by simpa using hq)
    exact hh'
  have hL : (2 : ℕ) ^ h ≤ N / 16 := Nat.pow_log_le_self 2 (by omega)
  have hU : N / 16 < (2 : ℕ) ^ (h + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have hl : 16 * 2 ^ h ≤ N := by omega
  have hu : N < 32 * 2 ^ h := by
    rw [pow_succ] at hU
    omega
  let A := (2 ^ (h + 1) - 1) * 2 + 8 * 2 ^ h
  have ha : A ≤ N := by
    unfold A
    rw [pow_succ]
    omega
  refine ⟨h, N - A, hh, hl, hu, ⟨Fintype.equivOfCardEq ?_⟩⟩
  simp only [TreeAction, Fintype.card_fin, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_bool, card_treeNode]
  unfold A at ha ⊢
  omega

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

@[simp] theorem rewardTapePrefix_refl (N r : ℕ) :
    rewardTapePrefix N (le_refl r) = id := by simp [rewardTapePrefix]

@[simp] theorem rewardTapePrefix_succ (N : ℕ) {r t : ℕ} (h : r ≤ t) :
    rewardTapePrefix N (Nat.le_succ_of_le h) = rewardTapePrefix N h ∘ Prod.fst := by
  unfold rewardTapePrefix
  exact Nat.leRec_succ _ _ h

theorem rewardTapePrefix_comp (N : ℕ) {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    rewardTapePrefix N hrs ∘ rewardTapePrefix N hst = rewardTapePrefix N (hrs.trans hst) := by
  induction hst with
  | refl => simp
  | step hs ih =>
    rw [rewardTapePrefix_succ N hs, rewardTapePrefix_succ N (hrs.trans hs)]
    funext tape
    exact congrFun ih tape.1

open scoped ENNReal

theorem boundedRoundReward_mem {N : ℕ} {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (u : ℝ) (i : Fin N) (d : ℝ × (Fin N → ℝ)) :
    boundedRoundReward η u i d ∈ Icc (0 : ℝ) 1 := by
  let z := (supportedBase d.1 : ℝ)
  have hz₀ : 0 ≤ z := (supportedBase d.1).property.1
  have hz₁ : z ≤ 1 := (supportedBase d.1).property.2
  have hsub : 0 ≤ 1 - z := sub_nonneg.mpr hz₁
  have hprod : 0 ≤ η / 8 * z * (1 - z) := by positivity
  have hηz : η / 8 * z ≤ 1 / 8 := by
    calc
      _ ≤ (1 / 8 : ℝ) * z := mul_le_mul_of_nonneg_right (by linarith) hz₀
      _ ≤ 1 / 8 := mul_le_of_le_one_right (by positivity) hz₁
  have hp : η / 8 * z * (1 - z) ≤ 1 / 8 := by
    exact (mul_le_mul_of_nonneg_right hηz hsub).trans
      (mul_le_of_le_one_right (by positivity) (by linarith))
  unfold boundedRoundReward bonusReward
  change (1 / 8 + z / 8 + η / 8 * z * (1 - z) * (if _ then 1 else 0) : ℝ) ∈ Icc 0 1
  split <;> simp only [mul_one, mul_zero] <;> exact ⟨by linarith, by linarith⟩

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set

theorem rawTapeHistory_eq_feedbackHistory {N T : ℕ} (η : ℝ) (u : ℕ → Fin N → ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (tape : RewardTape N T) (t : ℕ) (ht : t ≤ T) :
    rawTapeHistory η u pick t (rewardTapePrefix N ht tape) =
      feedbackHistory pick (fun s i => boundedRoundReward η (u s i) i (tapeDraw tape s)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he : (rewardTapePrefix N ht tape).1 = rewardTapePrefix N ((Nat.le_succ t).trans ht) tape := by
      have hf : rewardTapePrefix N (Nat.le_succ t) = (Prod.fst : RewardTape N (t + 1) → RewardTape N t) := by
        rw [rewardTapePrefix_succ N (le_refl t), rewardTapePrefix_refl, Function.id_comp]
      have hc := congrFun (rewardTapePrefix_comp N (Nat.le_succ t) ht) tape
      rw [hf] at hc
      exact hc
    have hdraw : tapeDraw tape t = (rewardTapePrefix N ht tape).2 := by
      simp only [tapeDraw, dif_pos (Nat.lt_of_succ_le ht)]
    have hhist := ih ((Nat.le_succ t).trans ht)
    simp only [rawTapeHistory, feedbackHistory, he, hhist, hdraw]
    rfl

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

theorem swapRegret_congr_before {N T : ℕ} {y y' : ℕ → Fin N → ℝ}
    {I I' : ℕ → Fin N}
    (hy : ∀ t < T, ∀ i, y t i = y' t i) (hI : ∀ t < T, I t = I' t) :
    swapRegret T y I = swapRegret T y' I' := by
  unfold swapRegret
  congr 1
  funext f
  exact Finset.sum_congr rfl fun t ht => by
    have ht' := Finset.mem_range.mp ht
    rw [hI t ht', hy t ht', hy t ht']

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory Set Filter

theorem tree_horizon_eq (h : ℕ) :
    2 ^ h * treePeriodLength h = treeActionBudget h ^ 4 := by
  unfold treePeriodLength treeActionBudget
  ring

theorem treeBonusScale_pos (h : ℕ) : 0 < treeBonusScale h := by unfold treeBonusScale treeActionBudget treeHeight; positivity

theorem treeBonusScale_lt_one (h : ℕ) : treeBonusScale h < 1 := by
  unfold treeBonusScale
  have hk : (16 : ℝ) ≤ treeActionBudget h := by
    unfold treeActionBudget
    have hpow : 0 < (2 : ℕ) ^ h := by positivity
    exact_mod_cast (show 16 ≤ 16 * 2 ^ h by omega)
  have hh : 1 ≤ treeHeight h := by unfold treeHeight; linarith only [Nat.cast_nonneg (α := ℝ) h]
  apply (div_lt_one (by positivity)).mpr
  nlinarith only [hk, hh, mul_nonneg (show 0 ≤ (treeActionBudget h : ℝ) by positivity) (sub_nonneg.mpr hh)]

theorem swapRegret_eq_of_zero_tail {N T T' : ℕ} (hTT : T ≤ T') (y : ℕ → Fin N → ℝ)
    (I : ℕ → Fin N) (hzero : ∀ t, T ≤ t → ∀ i, y t i = 0) :
    swapRegret T' y I = swapRegret T y I := by
  unfold swapRegret
  congr 1
  funext f
  symm
  refine Finset.sum_subset (Finset.range_mono hTT) ?_
  intro t _ ht
  have ht' : T ≤ t := Nat.le_of_not_gt fun hlt => ht (Finset.mem_range.mpr hlt)
  simp [hzero t ht']

end CalibeatBandit

open CalibeatBandit MeasureTheory Set Filter in
/-- Theorem 4.1. Every randomized measurable bandit policy at horizon N⁴
has a deterministic oblivious reward sequence with the stated lower rate. -/
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
        (pick : (t : ℕ) → S → FeedbackHistory t → Fin N),
        (∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2)) →
        ∃ y : ℕ → Fin N → ℝ, (∀ t i, y t i ∈ Icc 0 1) ∧
          c * (N : ℝ) ^ 3 / (Real.log N) ^ 6 ≤
            ∫ s, swapRegret (N ^ 4) y (fun t => pick t s (feedbackHistory (fun i => pick i s) y t)) ∂P := by
  obtain ⟨K₀, hK₀, hscale⟩ := tree_scale_threshold
  refine ⟨1 / (8 * 10 ^ 10), by positivity, 2 * K₀, ?_⟩
  intro N hN S inst P prob pick hm
  obtain ⟨h, U, hh, hKN, hNK, ⟨e⟩⟩ := exists_treeAction_equiv N (by omega)
  let r := treePeriodLength h
  let T := 2 ^ h * r
  let η := treeBonusScale h
  let active := blockLeaf h r
  let K := treeActionBudget h
  have hKN' : K ≤ N := hKN
  have hNK' : N < 2 * K := by unfold K treeActionBudget; omega
  have hKb : K₀ ≤ K := by omega
  let anchor : Fin N := ⟨0, by omega⟩
  obtain ⟨env, henv⟩ := exists_hard_tree_environment P hh hKN' hNK'.le hKb hscale e pick hm anchor
  let y₀ := treeEnvironmentReward e active η env
  let y (t : ℕ) (i : Fin N) := if t < T then y₀ t i else 0
  refine ⟨y, ?_, ?_⟩
  · intro t i
    unfold y
    split
    · exact boundedRoundReward_mem (treeBonusScale_pos h).le (treeBonusScale_lt_one h).le _ _ _
    · norm_num
  have hT : T ≤ N ^ 4 := (tree_horizon_eq h).le.trans (Nat.pow_le_pow_left hKN' 4)
  have hreg (s : S) :
      swapRegret (N ^ 4) y (fun t => pick t s (feedbackHistory (fun i => pick i s) y t)) =
        swapRegret T y₀ (treeEnvironmentAction e active η (fun t => pick t s) anchor env) := by
    rw [swapRegret_eq_of_zero_tail hT y _ (fun t ht i => if_neg (not_lt_of_ge ht))]
    apply swapRegret_congr_before (fun t ht i => if_pos ht)
    intro t ht
    have hh' := feedbackHistory_eq_of_prior_rewards_eq (fun n => pick n s) y y₀ t
      (fun t' ht' i => if_pos (ht'.trans ht))
    rw [hh']
    have ht' : t < 2 ^ h * treePeriodLength h := ht
    simp only [treeEnvironmentAction, dif_pos ht']
    rw [rawTapeHistory_eq_feedbackHistory]
    all_goals rfl
  simp_rw [hreg]
  convert henv using 1
  ring

end
