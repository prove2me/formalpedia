-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.eq_of_out_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:13:58.742966+00:00
-- url     : https://prove2.me/submissions/d4d49c52-c53a-4bdb-ad37-3181fcad78dd

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution (A₀ : AddSubgroup A) (q q' : A ⧸ A₀) (h : q.out - q'.out ∈ A₀) : q = q' := by
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
  symm
  rw [QuotientAddGroup.eq]
  have e : -q'.out + q.out = q.out - q'.out := by abel
  rwa [e]
end Formalism.L2.PairingIndexBounds.Mv
