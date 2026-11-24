-- Prove2me | solution 1 for Formalism.L2.SG.ClassAct.Normalises.inv_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:17.723824+00:00
-- url     : https://prove2.me/submissions/87bbdaa6-640d-4c6c-b483-e1ea6ae2bbe5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ClassAct
open Formalism.UG Module
variable {G : Type} [Group G]
namespace Formalism.L2.SG.ClassAct
namespace Normalises
theorem _root_.solution {D K : Subgroup G} (h : Normalises D K) {δ : G} (hδ : δ ∈ D) {κ : G}
    (hκ : κ ∈ K) : δ⁻¹ * κ * δ ∈ K := by
  have := h δ⁻¹ (D.inv_mem hδ) κ hκ
  simpa using this
end Normalises
end Formalism.L2.SG.ClassAct
