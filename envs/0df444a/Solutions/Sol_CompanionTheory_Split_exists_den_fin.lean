-- Prove2me | solution 1 for CompanionTheory.Split.exists_den_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:40.63841+00:00
-- url     : https://prove2.me/submissions/a258c48e-809c-409d-be8a-34d278a942ec

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_CompanionTheory_Split_exists_den
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
theorem _root_.solution {T : Set (GA L n)} (hT : T.Finite) :
    ∃ c : ℕ, c ≠ 0 ∧ ∀ t ∈ T, ∀ i j, (c : AL L) * ent t i j ∈ ALint L := by
  have := hT.fintype
  choose c h0 h using fun p : T × Fin n × Fin n => exists_den (ent p.1.1 p.2.1 p.2.2)
  refine ⟨∏ p, c p, Finset.prod_ne_zero_iff.2 fun p _ => h0 p, fun t ht i j => ?_⟩
  obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ (⟨t, ht⟩, i, j))
  rw [he, mul_comm _ e, Nat.cast_mul, mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ e) (h (⟨t, ht⟩, i, j))
end CompanionTheory.Split
