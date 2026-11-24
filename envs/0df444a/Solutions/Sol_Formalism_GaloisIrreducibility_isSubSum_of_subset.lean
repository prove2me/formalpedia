-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.isSubSum_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:43.039748+00:00
-- url     : https://prove2.me/submissions/01ef469c-5914-4d63-a2e9-14043fe03832

import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_IrredOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset
namespace Formalism.GaloisIrreducibility
theorem _root_.solution {ι : Type} (f : ι → ℕ) (I J : Finset ι) (hJ : J ⊆ I) :
    IsSubSum (I.val.map f) (∑ i ∈ J, f i) := by
  unfold IsSubSum
  exact ⟨J.val.map f, Multiset.map_le_map (Finset.val_le_iff.2 hJ), rfl⟩
end Formalism.GaloisIrreducibility
