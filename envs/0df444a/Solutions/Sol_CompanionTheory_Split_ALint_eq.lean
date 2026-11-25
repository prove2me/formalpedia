-- Prove2me | solution 1 for CompanionTheory.Split.ALint_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:06:04.370477+00:00
-- url     : https://prove2.me/submissions/e753a449-2447-432c-8aa4-a744703aa4d6

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
namespace CompanionTheory.Split
theorem _root_.solution : ALint L = tensInt (F := L⁺) (AFplus L) (intOE L) (intAd L⁺) := by
  rw [ALint, tensInt]
  congr 2 <;> ext x
  · exact ⟨fun ⟨y, h⟩ => ⟨⟨y, y, rfl⟩, h.symm⟩, fun ⟨⟨_, y, rfl⟩, h⟩ => ⟨y, h.symm⟩⟩
  · exact ⟨fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h.symm⟩, fun ⟨⟨a, ha⟩, h⟩ => ⟨a, ha, h.symm⟩⟩
end CompanionTheory.Split
