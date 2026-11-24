-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GoodRecipPf.rev_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:14.409642+00:00
-- url     : https://prove2.me/submissions/a9c62538-dd72-4c79-b336-3e241d4f650d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_GoodRecipPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GoodRecipPf
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.GoodRecipPf
theorem _root_.solution {q : K[X]} (h : q.coeff 0 ≠ 0) : q.reverse.natDegree = q.natDegree := by
  have ht : q.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr h)
  rw [reverse_natDegree, ht, Nat.sub_zero]
end Formalism.L2.SG.Pf.GoodRecipPf
