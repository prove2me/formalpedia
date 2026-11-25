-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.dyadic_size_le_pow_twelve_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:39.840644+00:00
-- url     : https://prove2.me/submissions/c8d79650-b2e2-427d-9424-a48dfda24b77

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DyadicSizeLePowTwelveSecond

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
theorem _root_.solution (q : ℕ) (hq : 256 ≤ q) : q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1)) ≤ q ^ 12 := by
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ (8 * (Nat.log 2 q + 1)) = 256 * (2 ^ Nat.log 2 q) ^ 8 := by
    rw [← pow_mul]; rw [show 8 * (Nat.log 2 q + 1) = 8 + Nat.log 2 q * 8 by ring, pow_add]; norm_num
  rw [h2]
  calc q ^ 3 * (256 * (2 ^ Nat.log 2 q) ^ 8) ≤ q ^ 3 * (q * q ^ 8) := by gcongr
    _ = q ^ 12 := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
