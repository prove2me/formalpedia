-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_size_le_pow_twelve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:50.246467+00:00
-- url     : https://prove2.me/submissions/29a08511-86bc-4589-85d2-d7dfe8bf7578

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
theorem _root_.solution (q : ℕ) (hq : 512 ≤ q) :
    2 * (q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1))) ≤ q ^ 12 := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  generalize Nat.log 2 q = n at hpow ⊢
  have h8 : 2 ^ (8 * (n + 1)) = 256 * (2 ^ n) ^ 8 := by
    rw [show 8 * (n + 1) = n * 8 + 8 by ring, pow_add, pow_mul]
    ring
  have h9 : (2 ^ n) ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hpow 8
  rw [h8]
  calc 2 * (q ^ 3 * (256 * (2 ^ n) ^ 8)) ≤ 2 * (q ^ 3 * (256 * q ^ 8)) := by gcongr
    _ = 512 * q ^ 11 := by ring
    _ ≤ q * q ^ 11 := by gcongr
    _ = q ^ 12 := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
