-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.root_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:18.365956+00:00
-- url     : https://prove2.me/submissions/165d48a2-8861-4aff-bfcb-fc8e57d7a5b2

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_frobenius_orbit_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {f : K[X]} (hm : f.Monic) (hi : Irreducible f) {x y : L} (hx : aeval x f = 0)
    (hy : aeval y f = 0) : ∃ n : ℕ, y = x ^ Fintype.card K ^ n := by
  classical
  have h := (frobenius_orbit_irreducible K L f hm hi).1.2
  have mem : ∀ z : L, aeval z f = 0 → z ∈ (f.aroots L).toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_aroots]
    exact ⟨hi.ne_zero, hz⟩
  obtain ⟨n, hn⟩ := h x (by convert mem x hx) y (by convert mem y hy)
  refine ⟨n, ?_⟩
  rw [← hn, pow_iterate]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
