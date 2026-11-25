-- Prove2me | solution 1 for CompanionTheory.Split.mem_UJ_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:32.169187+00:00
-- url     : https://prove2.me/submissions/db4b51ee-8199-491f-9e6f-5fc73cdc0c24

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
theorem _root_.solution {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (g : GL (Fin n) A) :
    g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ↔ g ∈ UGroup n σ hσ := by
  show cT σ (g : Matrix (Fin n) (Fin n) A) * 1 * g = 1 ↔ (g : Matrix (Fin n) (Fin n) A) * conjT σ g = 1
  rw [Matrix.mul_one]
  exact mul_eq_one_comm
end CompanionTheory.Split
