-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_binomialUpperTail_le_stirlingCore_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:41.797144+00:00
-- url     : https://prove2.me/submissions/b69378f3-33d0-4318-9583-0a3367d074cc

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_binomialUpperTail_le_first_of_fractional_gap
import Theorems.Thm_FirstPassageLinearTransport_exists_choose_le_stirlingCore_ratio

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r k : ℕ, 0 < r → 0 < k → k < r →
        (r : ℝ) * (1 / 2 + t₀) ≤ (k : ℝ) →
        (binomialUpperTail r k : ℝ) ≤
          C * stirlingCore r /
            (stirlingCore k * stirlingCore (r - k)) := by
  obtain ⟨C₀, hC₀, hchoose⟩ := exists_choose_le_stirlingCore_ratio
  refine ⟨(1 / (2 * t₀)) * C₀,
    mul_pos (one_div_pos.mpr (mul_pos (by norm_num) ht₀)) hC₀, ?_⟩
  intro r k hr hk hkr hgap
  have htail := binomialUpperTail_le_first_of_fractional_gap
    ht₀ hr hkr.le hgap
  have hfirst := hchoose r k hk hkr
  have hfactor0 : 0 ≤ 1 / (2 * t₀) :=
    (one_div_pos.mpr (mul_pos (by norm_num) ht₀)).le
  calc
    (binomialUpperTail r k : ℝ) ≤
        (1 / (2 * t₀)) * (r.choose k : ℝ) := htail
    _ ≤ (1 / (2 * t₀)) *
        (C₀ * stirlingCore r /
          (stirlingCore k * stirlingCore (r - k))) :=
      mul_le_mul_of_nonneg_left hfirst hfactor0
    _ = ((1 / (2 * t₀)) * C₀) * stirlingCore r /
          (stirlingCore k * stirlingCore (r - k)) := by ring
end FirstPassageLinearTransport
