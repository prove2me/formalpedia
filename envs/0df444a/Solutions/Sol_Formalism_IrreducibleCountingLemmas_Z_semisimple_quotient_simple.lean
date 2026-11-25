-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.semisimple_quotient_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:15.310418+00:00
-- url     : https://prove2.me/submissions/d0559e9d-1a13-4f09-81b0-f4fc7d69cc5b

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : SemisimpleQuotientSimple := by
  intro R M Q _ _ _ _ _ _ _ π huniq hπ
  have hco : ∀ C : Submodule R Q, IsCoatom C → IsCoatom (C.comap π) := by
    intro C hC
    refine ⟨?_, ?_⟩
    · intro h
      apply hC.1
      have := congrArg (Submodule.map π) h
      rwa [Submodule.map_comap_eq_of_surjective hπ, Submodule.map_top, LinearMap.range_eq_top.2 hπ]
        at this
    · intro b hb
      have hker : LinearMap.ker π ≤ b := le_trans (LinearMap.ker_le_comap π) hb.le
      have hbb : (b.map π).comap π = b := by
        rw [Submodule.comap_map_eq, sup_eq_left.2 hker]
      have hle : C ≤ b.map π := by
        have := Submodule.map_mono (f := π) hb.le
        rwa [Submodule.map_comap_eq_of_surjective hπ] at this
      have hne : C ≠ b.map π := by
        intro h
        rw [h, hbb] at hb
        exact lt_irrefl _ hb
      have htop := hC.2 _ (lt_of_le_of_ne hle hne)
      rw [← hbb, htop, Submodule.comap_top]
  have hone : ∀ C C' : Submodule R Q, IsCoatom C → IsCoatom C' → C = C' := by
    intro C C' hC hC'
    exact Submodule.comap_injective_of_surjective hπ (huniq _ _ (hco C hC) (hco C' hC'))
  rw [isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  by_contra hcon
  push Not at hcon
  obtain ⟨hbot, htop⟩ := hcon
  obtain ⟨N', hN'⟩ := exists_isCompl N
  have hN'top : N' ≠ ⊤ := by
    intro h
    apply hbot
    have := hN'.inf_eq_bot
    rwa [h, inf_top_eq] at this
  obtain ⟨C, hC, hNC⟩ := (eq_top_or_exists_le_coatom N).resolve_left htop
  obtain ⟨C', hC', hNC'⟩ := (eq_top_or_exists_le_coatom N').resolve_left hN'top
  have := hone C C' hC hC'
  subst this
  apply hC.1
  rw [eq_top_iff, ← hN'.sup_eq_top]
  exact sup_le hNC hNC'
end Formalism.IrreducibleCountingLemmas.Z
