-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.472822+00:00
-- url     : https://prove2.me/submissions/e726863e-8bb1-4c46-a95a-cfa5a78e9105

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : G) :
    (centralIdem ρ).coeff x =
      (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character x⁻¹ := by
  classical
  unfold centralIdem
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single x]
  · simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
  · intro b _ hb
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, hb]
  · intro h; exact absurd (Finset.mem_univ x) h
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
