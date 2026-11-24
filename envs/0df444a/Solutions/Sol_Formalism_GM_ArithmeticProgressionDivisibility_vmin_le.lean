-- Prove2me | solution 1 for Formalism.GM.ArithmeticProgressionDivisibility.vmin_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:25.355653+00:00
-- url     : https://prove2.me/submissions/2b116342-47bb-40b1-91a2-add9b8d52da1

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
open Formalism.GM.ArithmeticProgressionDivisibility
variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]
omit [NormedAlgebra ℚ_[p] K]
namespace Formalism.GM.ArithmeticProgressionDivisibility
theorem _root_.solution (h : ℕ) (x : K) :
    vmin p h x ≤ ∑ i ∈ Icc 1 h, (if ‖x‖ < (p : ℝ) ^ (1 - (i : ℤ)) then (1 : ℝ) else 0) := by
  have count : ∀ (r : ℝ) (n : ℕ),
      min r n ≤ ∑ i ∈ Icc 1 n, (if (i : ℝ) - 1 < r then (1 : ℝ) else 0) := by
    intro r n
    induction n with
    | zero =>
      rw [Finset.Icc_eq_empty (by omega)]
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      by_cases hc : ((n + 1 : ℕ) : ℝ) - 1 < r
      · rw [if_pos hc]
        have h1 : min r (n : ℝ) = n := min_eq_right (by linarith)
        have h2 := min_le_right r ((n + 1 : ℕ) : ℝ)
        linarith
      · rw [if_neg hc]
        have h1 : min r (n : ℝ) = r := min_eq_left (by linarith)
        have h2 := min_le_left r ((n + 1 : ℕ) : ℝ)
        linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpp : (0 : ℝ) < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  obtain ⟨M, hM⟩ : ∃ M, M = max ‖x‖ ((p : ℝ) ^ (-(h : ℤ))) := ⟨_, rfl⟩
  have hMge : (p : ℝ) ^ (-(h : ℤ)) ≤ M := by rw [hM]; exact le_max_right _ _
  have hxM : ‖x‖ ≤ M := by rw [hM]; exact le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le (zpow_pos hpp _) hMge
  have hr : vmin p h x = -(Real.log M / Real.log p) := by rw [hM]; rfl
  have hrh : vmin p h x ≤ h := by
    have h1 : ((-(h : ℤ) : ℤ) : ℝ) * Real.log p ≤ Real.log M := by
      rw [← Real.log_zpow]
      exact Real.log_le_log (zpow_pos hpp _) hMge
    have h2 : -(h : ℝ) ≤ Real.log M / Real.log p := by
      rw [le_div_iff₀ hlogp]
      push_cast at h1
      linarith
    rw [hr]
    linarith
  calc vmin p h x = min (vmin p h x) (h : ℝ) := (min_eq_left hrh).symm
    _ ≤ ∑ i ∈ Icc 1 h, (if (i : ℝ) - 1 < vmin p h x then (1 : ℝ) else 0) := count _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h1 : (i : ℝ) - 1 < vmin p h x
      · have h2 : ‖x‖ < (p : ℝ) ^ (1 - (i : ℤ)) := by
          have h3 : Real.log M / Real.log p < 1 - (i : ℝ) := by
            rw [hr] at h1
            linarith
          rw [div_lt_iff₀ hlogp] at h3
          have h4 : Real.log M < Real.log ((p : ℝ) ^ (1 - (i : ℤ))) := by
            rw [Real.log_zpow]
            push_cast
            linarith
          have h5 := (Real.log_lt_log_iff hMpos (zpow_pos hpp _)).mp h4
          linarith
        rw [if_pos h1, if_pos h2]
      · rw [if_neg h1]
        split_ifs <;> norm_num
end Formalism.GM.ArithmeticProgressionDivisibility
