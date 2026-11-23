-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.invSqrtPowLeExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:08.511058+00:00
-- url     : https://prove2.me/submissions/9f12c9cd-4da4-4f36-b40b-b27a6c5f68bd

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : GainSqrt := by
  intro k f b g hk hb hg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hk4pos : (0:ℝ) < (k:ℝ) ^ 4 := pow_pos hkpos 4
  have h8 : ((k:ℝ) ^ 4) ^ 2 ≤ g := by
    calc ((k:ℝ) ^ 4) ^ 2 = (k:ℝ) ^ 8 := by ring
      _ ≤ ((k:ℝ) * b) ^ 8 := pow_le_pow_left₀ hkpos.le (by nlinarith) 8
      _ ≤ g := hg
  have hk4 : (k:ℝ) ^ 4 ≤ Real.sqrt g := by
    calc (k:ℝ) ^ 4 = Real.sqrt (((k:ℝ) ^ 4) ^ 2) := (Real.sqrt_sq hk4pos.le).symm
      _ ≤ Real.sqrt g := Real.sqrt_le_sqrt h8
  have hinv : (Real.sqrt g)⁻¹ ≤ ((k:ℝ) ^ 4)⁻¹ := inv_anti₀ hk4pos hk4
  have e4 : Real.exp (4 * Real.log k) = (k:ℝ) ^ 4 := by
    rw [show (4:ℝ) * Real.log k = Real.log ((k:ℝ) ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log hk4pos]
  have heq : Real.exp (-4 * ((k:ℝ) * f * Real.log k)) = (((k:ℝ) ^ 4)⁻¹) ^ (k * f) := by
    rw [show -4 * ((k:ℝ) * f * Real.log k) = ((k * f : ℕ) : ℝ) * (-(4 * Real.log k)) by
      push_cast; try ring, Real.exp_nat_mul, Real.exp_neg, e4]
  rw [heq]
  exact pow_le_pow_left₀ (by positivity) hinv _
end Formalism.HermitianLatticeCounting.P
