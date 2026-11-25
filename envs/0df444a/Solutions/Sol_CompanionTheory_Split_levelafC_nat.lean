-- Prove2me | solution 1 for CompanionTheory.Split.levelafC_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:19.451321+00:00
-- url     : https://prove2.me/submissions/d7e40247-0c72-4795-a6f3-3926182dd37d

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
theorem _root_.solution (N : ℕ) : P.levelafC L (N : 𝓞 L⁺) = (N : AL L) := by
  rw [P.levelafC, map_natCast]
  exact map_natCast (Algebra.TensorProduct.includeRight (R := L⁺) (A := L) (B := AFplus L)) N
end CompanionTheory.Split
