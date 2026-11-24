-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.threshold_far_region
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:40.155043+00:00
-- url     : https://prove2.me/submissions/b9c20c19-8893-4f3a-b0c2-ed905f4ed6f8

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_log_ydat

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
theorem _root_.solution : ThreshFar := by
  intro C' c Cg hC' hc hCg
  refine ⟨C' * (Cg + 6) / c ^ 2, by positivity, ?_⟩
  intro n q f rd g b h hn hf hq hlf hb hrd hg hgb hh
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hqn : (q:ℝ)^2 ≤ n := by exact_mod_cast hq
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr hn'
  have hss : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hqs : (q:ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hqn
  have hlogn : Real.log n ≤ 2 * Real.sqrt n := by
    have h1 : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (n:ℝ) by linarith)
    linarith
  have hlb : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
  have hl2 := Real.log_two_gt_d9
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hlbr : Real.log (b * rd) = Real.log b + Real.log rd :=
    Real.log_mul (by positivity) (by positivity)
  have hlg : Real.log g ≤ Cg * Real.log b := by
    have := Real.log_le_log (by linarith) hgb
    rwa [Real.log_rpow (by linarith)] at this
  rw [hlbr] at hh
  have hY := log_ydat hn hf hrd hg hb
  set ℓ := Real.log b + Real.log rd with hℓ
  have hℓ0 : 0.69 ≤ ℓ := by linarith
  have hlY : Real.log (Ydat n f rd g b) ≤ 3 * Real.sqrt n + (Cg + 1) * ℓ := by
    rw [hY]
    have : Cg * Real.log b ≤ Cg * ℓ := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    linarith
  generalize Real.log (Ydat n f rd g b) = LY at *
  generalize Real.sqrt (n:ℝ) = s at *
  have k1 : (q:ℝ) * LY ≤ (Cg + 6) * (n * ℓ) := by
    calc (q:ℝ) * LY ≤ q * (3 * s + (Cg + 1) * ℓ) := by gcongr
      _ ≤ s * (3 * s + (Cg + 1) * ℓ) := by
          apply mul_le_mul_of_nonneg_right hqs
          have : 0 ≤ (Cg + 1) * ℓ := by positivity
          linarith
      _ = 3 * n + (Cg + 1) * (s * ℓ) := by rw [← hss]; ring
      _ ≤ 3 * n + (Cg + 1) * (n * ℓ) := by
          have : s ≤ n := by nlinarith
          gcongr
      _ ≤ _ := by nlinarith
  have e2 : epsN c n f ^ 2 = c ^ 2 / ((n:ℝ) ^ 16 * (f:ℝ) ^ 4) := by
    unfold epsN; rw [div_pow]; congr 1; ring
  have he0 : 0 ≤ epsN c n f ^ 2 := sq_nonneg _
  calc C' * (n:ℝ) ^ 2 * q * f * LY = C' * (n:ℝ) ^ 2 * f * (q * LY) := by ring
    _ ≤ C' * (n:ℝ) ^ 2 * f * ((Cg + 6) * (n * ℓ)) := by gcongr
    _ = (C' * (Cg + 6) / c ^ 2 * (n:ℝ) ^ 19 * (f:ℝ) ^ 5 * ℓ) * epsN c n f ^ 2 := by
        rw [e2]; field_simp
    _ ≤ h * epsN c n f ^ 2 := by gcongr
end Formalism.HermitianLatticeCounting.P
