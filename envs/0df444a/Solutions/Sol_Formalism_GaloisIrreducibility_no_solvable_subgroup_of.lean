-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.no_solvable_subgroup_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:43.205784+00:00
-- url     : https://prove2.me/submissions/c39c4b74-91d3-476b-83dd-dc76c9e76ca8

import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_NoSolvableOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : NoSolvableOf := by
  intro h1 h2 h3 h4 α _ _ G σ p hp hσG hpc hlt hge htrans hsolv
  obtain ⟨k, hk, hkc⟩ := h1 α σ p hp hpc hlt
  have hkG : σ ^ k ∈ G := G.pow_mem hσG k
  have hprim := h2 α G (σ ^ k) p hp hkG hk hkc hlt htrans
  have halt := h3 α G (σ ^ k) p hp hkG hk hkc hge hprim
  have h5 : 5 ≤ Fintype.card α := by have := hp.two_le; omega
  apply h4 α h5
  haveI := hsolv
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective halt)
end Formalism.GaloisIrreducibility
