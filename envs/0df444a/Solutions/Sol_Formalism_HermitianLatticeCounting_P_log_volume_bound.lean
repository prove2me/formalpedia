-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.log_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:35.730433+00:00
-- url     : https://prove2.me/submissions/43f1b816-74ca-47a8-bde5-cc0befc6ffe3

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LogVolumeBound := by
  intro a q f j C₁ Y hC hY hq hj
  have hY0 : 0 < Y := by linarith
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hCq : 1 ≤ C₁*q := by nlinarith
  have hpos : 0 < Y^(-(C₁*q)) := Real.rpow_pos_of_pos hY0 _
  have hle : Y^(-(C₁*q)) ≤ 1/2 := by
    rw [Real.rpow_neg hY0.le, one_div]
    apply inv_anti₀ (by norm_num)
    calc (2:ℝ) ≤ Y := hY
      _ = Y^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ Y^(C₁*q) := Real.rpow_le_rpow_of_exponent_le (by linarith) hCq
  refine ⟨hpos, hle, ?_⟩
  have hlog : Real.log (1/(2*Y^(-(C₁*q)))) = C₁*q*Real.log Y - Real.log 2 := by
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hpos.ne', Real.log_rpow hY0]; ring
  have hl0 : 0 ≤ Real.log (1/(2*Y^(-(C₁*q)))) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have hl1 : Real.log (1/(2*Y^(-(C₁*q)))) ≤ C₁*q*Real.log Y := by
    rw [hlog]; linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  calc ∏ x, (2*(f:ℝ)*j x * Real.log (1/(2*Y^(-(C₁*q))))) ≤ ∏ _x : Fin a, (2*C₁*f*(q:ℝ)^2*Real.log Y) := by
        apply Finset.prod_le_prod
        · intro x _; positivity
        · intro x _
          have : (j x:ℝ) ≤ q := by exact_mod_cast hj x
          calc 2*(f:ℝ)*j x * Real.log (1/(2*Y^(-(C₁*q)))) ≤ 2*(f:ℝ)*q*(C₁*q*Real.log Y) := by gcongr
            _ = _ := by ring
    _ = _ := by simp
end Formalism.HermitianLatticeCounting.P
