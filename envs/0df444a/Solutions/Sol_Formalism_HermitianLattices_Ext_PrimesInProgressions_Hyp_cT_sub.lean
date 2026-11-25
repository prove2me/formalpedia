-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cT_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:35:00.131061+00:00
-- url     : https://prove2.me/submissions/3c3e4a4d-9348-4923-b0fb-a0e48f19f509

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (U V : ℕ) (hUV : U ≤ V) :
    cT χ V - cT χ U = ∑ n ∈ Ioc U V, χ (n : ZMod q) * (lw n : ℂ) := by
  rw [cT, cT, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUV, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold lw; push_cast; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
