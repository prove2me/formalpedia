-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sum_of_mul_sum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:02.814545+00:00
-- url     : https://prove2.me/submissions/a8db052e-9be4-47f0-b70a-70fb3f6068f8

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent

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
variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (A B : G → ℂ) :
    (∑ g, A g • MonoidAlgebra.of ℂ G g) * (∑ g, B g • MonoidAlgebra.of ℂ G g) =
      ∑ k, (∑ g, A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by
  rw [Finset.sum_mul_sum]
  have key : ∀ g, ∑ h, (A g • MonoidAlgebra.of ℂ G g) * (B h • MonoidAlgebra.of ℂ G h) =
      ∑ k, (A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by
    intro g
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_congr rfl (fun g _ => key g), Finset.sum_comm]
  simp_rw [Finset.sum_smul]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
