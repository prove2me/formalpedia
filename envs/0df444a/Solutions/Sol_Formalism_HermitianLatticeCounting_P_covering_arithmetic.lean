-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.covering_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:20.550798+00:00
-- url     : https://prove2.me/submissions/3952a51e-762b-40e8-b107-1a6551519524

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
theorem _root_.solution : CoverArith := by
  intro n f N rd ρ hf hN hrd hρ
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hN' : (N:ℝ) ≤ 2 * (n:ℝ)^2 * f := by exact_mod_cast hN
  have hs0 : 0 < Real.sqrt (f:ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt (f:ℝ) * Real.sqrt (f:ℝ) = f := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt (f:ℝ) := Real.one_le_sqrt.mpr hf'
  have h52 : (f:ℝ)^((5:ℝ)/2) = (f:ℝ)^2 * Real.sqrt f := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; norm_num
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  rw [h52]
  generalize Real.sqrt (f:ℝ) = s at *
  have hfs : (f:ℝ) = s * s := hss.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have : 2 * (n:ℝ)^2 * s * rd * ρ * (s / (2 * rd * ρ)) = (n:ℝ)^2 * (s * s) := by field_simp
    rw [this, ← hfs]; linarith
  · rw [div_le_iff₀ (by positivity)]
    have : 8 * (n:ℝ)^4 * ((f:ℝ)^2 * s) * rd * ρ * (s / (2 * rd * ρ)) = 4 * (n:ℝ)^4 * (f:ℝ)^2 * (s * s) := by
      field_simp; ring
    rw [this, ← hfs]
    have h2 : (N:ℝ)^2 ≤ (2 * (n:ℝ)^2 * f)^2 := by gcongr
    have h3 : (2 * (n:ℝ)^2 * f)^2 * 1 ≤ (2 * (n:ℝ)^2 * f)^2 * f := by gcongr
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have : 8 * (n:ℝ)^6 * ((f:ℝ)^2 * s) * rd * ρ * (2 * (s / (2 * rd * ρ))) = 8 * (n:ℝ)^6 * (f:ℝ)^2 * (s * s) := by
      field_simp
    rw [this, ← hfs]
    have h2 : (N:ℝ)^3 ≤ (2 * (n:ℝ)^2 * f)^3 := by gcongr
    nlinarith
end Formalism.HermitianLatticeCounting.P
