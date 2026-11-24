-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.norm_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:26.598849+00:00
-- url     : https://prove2.me/submissions/44475f97-f31b-41e3-882f-dd3ef1fc4159

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_norm_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (hq : Fintype.card L = q ^ 2) :
    ((univ.erase (0 : L) : Finset L) : Set L).MapsTo (fun u => u ^ (q + 1)) (Sfix L q) := by
  intro u hu
  simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and] at hu
  simp only [Sfix, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
  exact ⟨pow_ne_zero _ hu, norm_fixed hq u⟩
end Formalism.LogVandermondeBounds.StandardLattice
