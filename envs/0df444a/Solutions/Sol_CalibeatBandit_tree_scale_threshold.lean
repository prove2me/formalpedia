-- Prove2me | solution 1 for CalibeatBandit.tree_scale_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:43:07.316555+00:00
-- url     : https://prove2.me/submissions/668f7080-d74e-43e6-b89c-46abee43f4a9

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal Function

/-- The information bound gives at most T/(64H) plays of the selected
auxiliary action in expectation after summing the equally long periods. -/
theorem auxiliary_rate_le {K H : ℝ} (hH : 1 ≤ H) (hK : 256 * H ≤ K) :
    K ^ 4 / (K / 2) + 1 / (1000 * K * H) * K ^ 4 *
        Real.sqrt ((K ^ 4 / (K / 16)) / (6 * (K / 2))) ≤ K ^ 4 / (64 * H) := by
  have hH₀ : 0 < H := by linarith
  have hK₀ : 0 < K := by linarith
  have he : (K ^ 4 / (K / 16)) / (6 * (K / 2)) = K ^ 2 * (16 / 3) := by
    field_simp
    norm_num
  have hs : Real.sqrt ((K ^ 4 / (K / 16)) / (6 * (K / 2))) ≤ 3 * K := by
    rw [he, Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK₀.le]
    have h : Real.sqrt (16 / 3 : ℝ) ≤ 3 :=
      (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_left h hK₀.le]
  have hm : K ^ 4 / (K / 2) ≤ K ^ 4 / (128 * H) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hB : 1 / (1000 * K * H) * K ^ 4 * (3 * K) ≤ K ^ 4 / (128 * H) := by
    field_simp
    nlinarith [show 0 ≤ K ^ 5 by positivity]
  have hb := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 1 / (1000 * K * H) * K ^ 4 by positivity)
  linarith only [hm, hB, hb, show K ^ 4 / (64 * H) = 2 * (K ^ 4 / (128 * H)) by ring]

/-- A logarithmic tree height meets the auxiliary-action budget for all
sufficiently large action sets. -/
theorem auxiliary_rate_condition_eventually :
    ∀ᶠ K : ℝ in atTop, ∀ H : ℝ, H ≤ 2 * Real.log K → 256 * H ≤ K := by
  have hsmall := Real.isLittleO_log_id_atTop.def (c := 1 / 512) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with K hs hK H hh
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  change ‖Real.log K‖ ≤ (1 / 512 : ℝ) * ‖K‖ at hs
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by linarith : 0 ≤ K)] at hs
  linarith

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open Filter
open scoped Topology

/-- The depth of the constructed tree satisfies the logarithmic height
estimate used in both the information bound and the final rate. -/
theorem treeHeight_le_log_scale (h : ℕ) :
    (h : ℝ) + 1 ≤ 2 * Real.log (16 * (2 : ℝ) ^ h) := by
  have hlog : 1 / 2 ≤ Real.log (2 : ℝ) := by
    have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hl
    exact hl
  have h16 : Real.log (16 : ℝ) = 4 * Real.log (2 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num) (by positivity), h16, Real.log_pow]
  have hn : 0 ≤ (h : ℝ) := by positivity
  nlinarith only [hlog, mul_nonneg hn (sub_nonneg.mpr hlog)]

/-- Extra unused actions permit arbitrary action budgets. Even for up to
twice the dyadic budget, the martingale error is smaller than the signal. -/
theorem tree_realized_rate_eventually :
    ∀ᶠ K : ℝ in atTop, ∀ N H : ℝ, K ≤ N → N ≤ 2 * K → 1 ≤ H → H ≤ 2 * Real.log K →
      let η := 1 / (1000 * K * H)
      N ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤
        η / 48 * (K ^ 4 / (368 * H ^ 5)) -
          N * (η / 16 * Real.sqrt (2 * K ^ 4 * Real.log (2 * N))) := by
  let C : ℝ := 1 / 100000000
  have hs := (isLittleO_log_rpow_rpow_atTop (s := 1) 7 (by norm_num)).def
    (c := C) (by norm_num [C])
  filter_upwards [hs, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (2 : ℝ)] with K hsmall hL hK N H hKN hNK hH hHmax η
  let L := Real.log K
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hK₀ : 0 < K := by linarith
  have hN₀ : 0 < N := hK₀.trans_le hKN
  have hH₀ : 0 < H := by linarith
  have hh : L ^ 7 ≤ C * K := by
    change ‖L ^ (7 : ℝ)‖ ≤ C * ‖K ^ (1 : ℝ)‖ at hsmall
    rw [show L ^ (7 : ℝ) = L ^ (7 : ℕ) by exact Real.rpow_ofNat L 7,
      Real.rpow_one, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hK₀.le] at hsmall
    exact hsmall
  have hlogN : L ≤ Real.log N := Real.log_le_log hK₀ hKN
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hK
  have hlog2N : Real.log (2 * N) ≤ 3 * L := by
    calc
      _ ≤ Real.log (4 * K) := Real.log_le_log (by positivity) (by linarith only [hNK])
      _ = 2 * Real.log 2 + L := by
        rw [Real.log_mul (by norm_num) hK₀.ne']
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num [L]
      _ ≤ _ := by linarith only [hlog2]
  have hlog2N₀ : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith only [hKN, hK])
  have hsmallSqrt : Real.sqrt (2 * Real.log (2 * N)) ≤ 3 * L := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [hlog2N, mul_nonneg hL₀.le (sub_nonneg.mpr hL)]
  have hsqrt : Real.sqrt (2 * K ^ 4 * Real.log (2 * N)) ≤ K ^ 2 * (3 * L) := by
    rw [show 2 * K ^ 4 * Real.log (2 * N) = (K ^ 2) ^ 2 * (2 * Real.log (2 * N)) by ring,
      Real.sqrt_mul (sq_nonneg (K ^ 2)), Real.sqrt_sq (sq_nonneg K)]
    exact mul_le_mul_of_nonneg_left hsmallSqrt (sq_nonneg K)
  have hη₀ : 0 ≤ η := by dsimp [η]; positivity
  have hη : η ≤ 1 / (1000 * K) := by
    dsimp [η]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (le_mul_of_one_le_right (by positivity) hH)
  have herr : N * (η / 16 * Real.sqrt (2 * K ^ 4 * Real.log (2 * N))) ≤ K ^ 2 * L / 2500 := by
    calc
      _ ≤ (2 * K) * ((1 / (1000 * K)) / 16 * (K ^ 2 * (3 * L))) := by
        gcongr
      _ = 3 * (K ^ 2 * L) / 8000 := by field_simp; ring
      _ ≤ _ := by nlinarith only [show 0 ≤ K ^ 2 * L by positivity]
  have herr' : K ^ 2 * L / 2500 ≤ K ^ 3 / (250000000000 * L ^ 6) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hz := mul_le_mul_of_nonneg_left hh (sq_nonneg K)
    norm_num [C] at hz
    nlinarith only [hz]
  have hsignal : η / 48 * (K ^ 4 / (368 * H ^ 5)) = K ^ 3 / (17664000 * H ^ 6) := by
    dsimp [η]
    field_simp
    ring
  have hmain : K ^ 3 / (1130496000 * L ^ 6) ≤ η / 48 * (K ^ 4 / (368 * H ^ 5)) := by
    rw [hsignal]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hp := pow_le_pow_left₀ hH₀.le hHmax 6
    change H ^ 6 ≤ (2 * L) ^ 6 at hp
    nlinarith only [hp]
  have htarget : N ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤ K ^ 3 / (10 ^ 10 * L ^ 6) := by
    calc
      _ ≤ (2 * K) ^ 3 / (8 * 10 ^ 10 * L ^ 6) := by
        gcongr
      _ = _ := by ring
  have hsum : K ^ 3 / (10 ^ 10 * L ^ 6) + K ^ 3 / (250000000000 * L ^ 6) ≤
      K ^ 3 / (1130496000 * L ^ 6) := by
    have h := div_nonneg (show 0 ≤ K ^ 3 by positivity) (show 0 ≤ L ^ 6 by positivity)
    rw [mul_comm (10 ^ 10 : ℝ), mul_comm (250000000000 : ℝ), mul_comm (1130496000 : ℝ),
      ← div_div, ← div_div, ← div_div]
    norm_num
    linarith
  linarith only [herr, herr', hmain, htarget, hsum]

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

/-- The information estimate and the numerical regret estimate both hold
uniformly once the dyadic budget is sufficiently large. -/
theorem tree_scale_threshold :
    ∃ K₀ : ℕ, 32 ≤ K₀ ∧ ∀ h N : ℕ,
      K₀ ≤ treeActionBudget h → treeActionBudget h ≤ N → N ≤ 2 * treeActionBudget h →
      let L := 2 ^ h
      let M : ℕ := 8 * L
      let r := treePeriodLength h
      let T := L * r
      let H := treeHeight h
      let η := treeBonusScale h
      ((L : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
        (T : ℝ) / (64 * H)) ∧
      ((N : ℝ) ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤
        η / 48 * ((T : ℝ) / (368 * H ^ 5)) -
          N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N)))) := by
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp auxiliary_rate_condition_eventually
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp tree_realized_rate_eventually
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (max 32 (max A B))
  have hK₀₃₂ : 32 ≤ K₀ := by exact_mod_cast (le_max_left (32 : ℝ) (max A B)).trans hK₀
  refine ⟨K₀, hK₀₃₂, ?_⟩
  intro h N hscale hKN hNK L M r T H η
  let K := treeActionBudget h
  have hscale' : (K₀ : ℝ) ≤ K := by exact_mod_cast hscale
  have ha : A ≤ (K : ℝ) := (le_max_left A B).trans ((le_max_right (32 : ℝ) _).trans (hK₀.trans hscale'))
  have hb : B ≤ (K : ℝ) := (le_max_right A B).trans ((le_max_right (32 : ℝ) _).trans (hK₀.trans hscale'))
  have hH : 1 ≤ H := by unfold H treeHeight; linarith only [Nat.cast_nonneg (α := ℝ) h]
  have hHlog : H ≤ 2 * Real.log K := by
    simpa [H, treeHeight, K, treeActionBudget] using treeHeight_le_log_scale h
  have hKr : (K : ℝ) = 16 * (L : ℝ) := by norm_num [K, L, treeActionBudget]
  have hM : (M : ℝ) = (K : ℝ) / 2 := by
    dsimp only [M]
    push_cast
    rw [hKr]
    ring
  have hTn : T = K ^ 4 := tree_horizon_eq h
  have hT : (T : ℝ) = (K : ℝ) ^ 4 := by exact_mod_cast hTn
  have hL : (L : ℝ) = (K : ℝ) / 16 := by rw [hKr]; ring
  have hLpos : 0 < (L : ℝ) := by unfold L; positivity
  have hTr : (L : ℝ) * (r : ℝ) = (T : ℝ) := by norm_num [T]
  have hr : (r : ℝ) = (K : ℝ) ^ 4 / ((K : ℝ) / 16) := by
    rw [← hL, ← hT, ← hTr, mul_comm]
    exact (mul_div_cancel_right₀ _ hLpos.ne').symm
  have hη : η = 1 / (1000 * (K : ℝ) * H) := rfl
  constructor
  · calc
      _ = (T : ℝ) / M + η * T * Real.sqrt ((r : ℝ) / (6 * M)) := by rw [← hTr]; ring
      _ ≤ _ := by rw [hM, hη, hT, hr]; exact auxiliary_rate_le hH (hA K ha H hHlog)
  · rw [hT, hη]
    exact hB K hb N H (by exact_mod_cast hKN) (by exact_mod_cast hNK) hH hHlog

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.tree_scale_threshold := @CalibeatBandit.tree_scale_threshold
