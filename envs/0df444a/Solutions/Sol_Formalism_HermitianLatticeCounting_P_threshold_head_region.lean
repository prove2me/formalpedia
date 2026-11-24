-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.threshold_head_region
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:40.552137+00:00
-- url     : https://prove2.me/submissions/6a03fb7a-b702-4414-888b-20425908ac94

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

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
theorem _root_.solution : ThreshHead := by
  intro C₂
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(120 + |C₂|) / Real.log 2, by positivity, ?_⟩
  intro n q f b rd h hn hf hq hb hrd hh
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hqn : (q:ℝ)^2 ≤ n := by exact_mod_cast hq
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  have hlog : Real.log 2 ≤ Real.log (b * rd) := Real.log_le_log (by norm_num) (by nlinarith)
  have h19 : 0 < (n:ℝ)^19 := by positivity
  have hK : (120 + |C₂|) * (n:ℝ)^19 ≤ h := by
    refine le_trans ?_ hh
    have h1 : (1:ℝ) ≤ (f:ℝ)^5 := one_le_pow₀ hf'
    have hA : 0 ≤ 120 + |C₂| := by positivity
    calc (120 + |C₂|) * (n:ℝ)^19 = (120 + |C₂|) / Real.log 2 * (n:ℝ)^19 * 1 * Real.log 2 := by
          field_simp
      _ ≤ (120 + |C₂|) / Real.log 2 * (n:ℝ)^19 * (f:ℝ)^5 * Real.log (b*rd) := by gcongr
  have hq32 : (q:ℝ)^((3:ℝ)/2) ≤ n := by
    rcases Nat.eq_zero_or_pos q with rfl | hqp
    · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; positivity
    · have h1 : (1:ℝ) ≤ q := by exact_mod_cast hqp
      calc (q:ℝ)^((3:ℝ)/2) ≤ (q:ℝ)^((2:ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = (q:ℝ)^2 := Real.rpow_two _
        _ ≤ n := hqn
  have hsq : Real.sqrt q ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hp2 : (n:ℝ)^2 ≤ (n:ℝ)^19 := pow_le_pow_right₀ hn' (by norm_num)
  have hp3 : (n:ℝ)^3 ≤ (n:ℝ)^19 := pow_le_pow_right₀ hn' (by norm_num)
  have hC : 0 ≤ |C₂| * (n:ℝ)^19 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc 120 * (n:ℝ) * (q:ℝ)^((3:ℝ)/2) ≤ 120 * (n:ℝ) * n := by gcongr
      _ = 120 * (n:ℝ)^2 := by ring
      _ ≤ h := by linarith
  · calc C₂ * (n:ℝ)^2 * Real.sqrt q ≤ |C₂| * (n:ℝ)^2 * n := by
          gcongr
          exact le_abs_self _
      _ = |C₂| * (n:ℝ)^3 := by ring
      _ ≤ |C₂| * (n:ℝ)^19 := by gcongr
      _ ≤ h := by linarith
  · calc 32 * (n:ℝ) * q ≤ 32 * (n:ℝ) * n := by gcongr
      _ = 32 * (n:ℝ)^2 := by ring
      _ < h := by linarith
end Formalism.HermitianLatticeCounting.P
