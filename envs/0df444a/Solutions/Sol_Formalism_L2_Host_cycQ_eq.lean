-- Prove2me | solution 1 for Formalism.L2.Host.cycQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:31.291523+00:00
-- url     : https://prove2.me/submissions/bfeb7f40-2e05-48fb-8e66-922fd572fde2

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.L2.Host
theorem _root_.solution {N : ℕ} [NeZero N] {w : Qb} (hw : IsPrimitiveRoot w N) : cycQ N = ℚ⟮w⟯ := by
  apply le_antisymm
  · show adjoin ℚ (mus N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ w) i
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ (mus N) hw.pow_eq_one
end Formalism.L2.Host
