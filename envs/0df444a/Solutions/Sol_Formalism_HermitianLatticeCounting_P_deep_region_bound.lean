-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.deep_region_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:05.9618+00:00
-- url     : https://prove2.me/submissions/81335181-370b-4998-96e3-63d914857f81

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_le_rpow_two_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ydat_facts
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_b1_bound_le_power
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_deep_region_bound_height

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DeepBound := by
  intro C hC
  obtain ⟨C₁, hC₁, H⟩ := deep_region_bound_height (2 * C + 18) (by linarith)
  refine ⟨C₁, hC₁, ?_⟩
  intro n q f rd g b hn hq hqn hf hrd hg hb
  obtain ⟨hY, hnY, hfY, hrdY, hgY, hbY⟩ := ydat_facts hn hf hrd hg hb
  have hqn' : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
  have hb1 := b1_bound_le_power (f := f) hqn' hY hnY hfY (by linarith) hbY
  have H' := H n q f _ hq hY
  generalize Ydat n f rd g b = Y at *
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  refine le_trans ?_ H'
  have hb10 : 0 ≤ b1 n q f b := by unfold b1; positivity
  have hbr : C * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b1 n q f b ≤ Y ^ (2 * C + 18) := by
    have e : Y ^ (2 * C + 18) = Y ^ (2 * C) * Y ^ 4 * Y ^ 2 * Y * Y * Y ^ 10 := by
      rw [Real.rpow_add hY0]
      have : Y ^ (18:ℝ) = Y ^ 18 := by exact_mod_cast Real.rpow_natCast Y 18
      rw [this]; ring
    rw [e]
    have := le_rpow_two_mul hY (by linarith : 0 ≤ C)
    gcongr
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc Y ^ (C * (n:ℝ) ^ 2 * f) * (C * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
      ≤ Y ^ (C * (n:ℝ) ^ 2 * f) * (Y ^ (2 * C + 18)) ^ (16 * q * n ^ 2 * f) := by
        gcongr
    _ = Y ^ (C * (n:ℝ) ^ 2 * f + (2 * C + 18) * ((16 * q * n ^ 2 * f : ℕ) : ℝ)) := by
        rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hY1
        push_cast
        have hm0 : 0 ≤ (n:ℝ) ^ 2 * f := by positivity
        nlinarith
end Formalism.HermitianLatticeCounting.P
