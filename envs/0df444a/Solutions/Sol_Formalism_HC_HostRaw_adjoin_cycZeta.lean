-- Prove2me | solution 1 for Formalism.HC.HostRaw.adjoin_cycZeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:28:19.635399+00:00
-- url     : https://prove2.me/submissions/017c535f-1443-4e38-8730-ff887082718b

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta

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
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.L2.Host
variable {φ : Frame} (H : HostRaw φ)
variable {H}
variable (H)
namespace Formalism.HC.HostRaw
theorem _root_.solution : IntermediateField.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : x ∈ Algebra.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN)) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim]; trivial
  exact algebra_adjoin_le_adjoin ℚ _ h1
end Formalism.HC.HostRaw
