-- Prove2me | solution 1 for Formalism.L2.Host.CharEx.mem_unitIdeles_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:00:08.166304+00:00
-- url     : https://prove2.me/submissions/0078e45c-2327-4cab-8acd-d52d608f73c2

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_rayUnits_top_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.L2.Host.CharEx
variable (L : Type) [Field L] [NumberField L]
namespace Formalism.L2.Host.CharEx
theorem _root_.solution (u : Ideles L) : u ∈ unitIdeles L ↔ u ∈ rayUnits L ⊤ ∅ := by
  rw [rayUnits_top_iff]
  exact Iff.rfl
end Formalism.L2.Host.CharEx
