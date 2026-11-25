-- Prove2me | solution 1 for CompanionTheory.Split.reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:35:10.675138+00:00
-- url     : https://prove2.me/submissions/608bcd54-177f-4e4c-8a32-1cd8a7ae5903

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_CompanionTheory_Split_reps_Umax
import Theorems.Thm_CompanionTheory_Split_reps_Cong
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
theorem _root_.solution {N : ℕ} (hN : N ≠ 0) :
    ∃ T : Set (GA L n), T.Finite ∧ ∀ g, ∃ γ ∈ GQ L n, ∃ t ∈ T, ∃ κ, NG.Cong L n N κ ∧ g = γ * t * κ := by
  obtain ⟨T, hT, h⟩ := reps_Umax (L := L) (n := n)
  obtain ⟨T', hT', h'⟩ := reps_Cong (L := L) (n := n) hN
  refine ⟨Set.image2 (· * ·) T T', hT.image2 _ hT', fun g => ?_⟩
  obtain ⟨γ, hγ, t, ht, κ, hκ, rfl⟩ := h g
  obtain ⟨t', ht', hc⟩ := h' κ hκ
  exact ⟨γ, hγ, t * t', Set.mem_image2_of_mem ht ht', _, hc, by group⟩
end CompanionTheory.Split
