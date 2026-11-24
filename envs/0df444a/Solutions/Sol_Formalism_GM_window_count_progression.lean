-- Prove2me | solution 1 for Formalism.GM.window_count_progression
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:31.595091+00:00
-- url     : https://prove2.me/submissions/aa4e6d04-70a9-496f-b888-f6a956cb9e3e

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_vmin_le
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_card_le

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
open ArithmeticProgressionDivisibility
namespace Formalism.GM
theorem _root_.solution : WindowCountAP := by
  intro p _ K _ _ _ ζ t₀ d Y₀ h hd
  calc ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ)
      ≤ ∑ j ∈ range Y₀, ∑ i ∈ Icc 1 h,
          (if ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun j _ => vmin_le h _
    _ = ∑ i ∈ Icc 1 h, ∑ j ∈ range Y₀,
          (if ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)) then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / (p : ℝ) ^ i + 1) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Finset.sum_boole]
        exact card_le ζ t₀ d hd Y₀ i
end Formalism.GM
