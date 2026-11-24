-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gelfand_trick
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:36.530792+00:00
-- url     : https://prove2.me/submissions/f6383a34-35f4-4f85-a63c-01d7df453174

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Bl_CyclicComponents_goal1
import Theorems.Thm_Bl_general_b_fact_right_rest_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (J : Subgroup G) (χ : J →* ℂˣ)
    (hcomm : ∀ g g' : G, (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ))
    (hirr : IsIrr ρ) :
    Module.finrank ℂ (eqvSpace ρ (fun u : J => (u : G)) (fun u => ((χ u : ℂˣ) : ℂ))) ≤ 1 := by
  first | exact Bl.CyclicComponents.goal1 .. | (apply Bl.CyclicComponents.goal1 <;> assumption) | (intros; apply Bl.CyclicComponents.goal1 <;> assumption) | (apply @Bl.CyclicComponents.goal1 <;> assumption) | (intros; apply @Bl.CyclicComponents.goal1 <;> assumption) | (apply @Bl.CyclicComponents.goal1 <;> first | assumption | infer_instance)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
