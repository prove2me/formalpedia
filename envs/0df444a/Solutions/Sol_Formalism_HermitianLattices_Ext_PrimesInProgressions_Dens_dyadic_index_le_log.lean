-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_index_le_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:45:48.365514+00:00
-- url     : https://prove2.me/submissions/7deded89-309c-4300-85c9-e04c001f4286

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_OneLeLogOfThreeLe
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_one_le_log_of_three_le__619f5b1cd3f0

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
theorem _root_.solution (q : ℕ) (hq : 3 ≤ q) :
    ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h1 : ((2 : ℝ) ^ Nat.log 2 q) ≤ q := by exact_mod_cast hpow
  have h2 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have hl2 := Real.log_two_gt_d9
  have hlq : 1 ≤ Real.log q := one_le_log_of_three_le' (by exact_mod_cast hq)
  have hn0 : (0 : ℝ) ≤ Nat.log 2 q := Nat.cast_nonneg _
  have h3 : 0.6931471803 * (Nat.log 2 q : ℝ) ≤ Real.log q := by nlinarith
  push_cast
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
