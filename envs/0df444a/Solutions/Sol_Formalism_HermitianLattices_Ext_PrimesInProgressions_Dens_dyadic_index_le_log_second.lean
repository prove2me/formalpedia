-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_index_le_log_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:17:04.664895+00:00
-- url     : https://prove2.me/submissions/b1e682f8-1458-40bb-ac21-dc6b6dd09008

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DyadicSizeLePowTwelveSecond
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_one_le_log_of_three_le_second

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
theorem _root_.solution (q : ℕ) (hq : 3 ≤ q) : ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) ≤ 24 * Real.log q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 q ≤ q := by exact_mod_cast h1
  have h3 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2
  have h4 := Real.log_two_gt_d9
  have h5 := one_le_log_of_three_le_second hq'
  have h6 : (0 : ℝ) ≤ (Nat.log 2 q : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
