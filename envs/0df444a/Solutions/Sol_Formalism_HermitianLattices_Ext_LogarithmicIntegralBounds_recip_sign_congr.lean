-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.recip_sign_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:18.780021+00:00
-- url     : https://prove2.me/submissions/47a2f29a-5110-48fc-95d5-a58b29be3692

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqJac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (p q q' : ℕ) (h4 : q % 4 = q' % 4) :
    ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ (p / 2 * (q' / 2)) := by
  have h : (q / 2) % 2 = (q' / 2) % 2 := by omega
  calc ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ ((p / 2 * (q / 2)) % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1) ^ ((p / 2 * (q' / 2)) % 2) := by rw [Nat.mul_mod, h, ← Nat.mul_mod]
    _ = (-1) ^ (p / 2 * (q' / 2)) := (neg_one_pow_eq_pow_mod_two _).symm
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
