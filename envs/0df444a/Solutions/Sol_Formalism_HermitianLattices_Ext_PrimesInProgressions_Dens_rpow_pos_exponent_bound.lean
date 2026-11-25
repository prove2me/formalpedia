-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.rpow_pos_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:13.084963+00:00
-- url     : https://prove2.me/submissions/68b3b0c8-750b-41c5-9cf4-679d9d827d03

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneLeLogOfThreeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have he : 0 ≤ 2 - 2 * σ := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hUq : (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
  have s1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((q : ℝ) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hUq he
  have s2 : ((q : ℝ) ^ 12) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) := by
    apply Real.rpow_le_rpow (by positivity) _ he
    gcongr
  have s3 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx.le]
    rw [show ((12 : ℕ) : ℝ) * (2 - 2 * σ) = 24 * (1 - σ) by push_cast; ring]
  have s4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    calc (2 : ℝ) ^ (24 * (1 - σ)) ≤ (2 : ℝ) ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 64 := by rw [Real.rpow_natCast]; norm_num
  have hx' : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  calc (U : ℝ) ^ (2 - 2 * σ) ≤ (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
        rw [← s3]; exact s1.trans s2
    _ ≤ 64 * x ^ (24 * (1 - σ)) := by gcongr
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
