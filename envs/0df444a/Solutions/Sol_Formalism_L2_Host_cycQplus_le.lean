-- Prove2me | solution 1 for Formalism.L2.Host.cycQplus_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:53:28.891802+00:00
-- url     : https://prove2.me/submissions/23cbb943-860b-440c-8989-8803967f5750

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast

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
theorem _root_.solution (N : ℕ) : cycQplus N ≤ cycQ N := by
  rw [cycQplus, adjoin_le_iff]
  rintro _ ⟨z, hz, rfl⟩
  have : z ∈ cycQ N := subset_adjoin ℚ _ hz
  exact add_mem this (inv_mem this)
end Formalism.L2.Host
