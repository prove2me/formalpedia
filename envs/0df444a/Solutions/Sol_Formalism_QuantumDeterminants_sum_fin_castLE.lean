-- Prove2me | solution 1 for Formalism.QuantumDeterminants.sum_fin_castLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:30.104214+00:00
-- url     : https://prove2.me/submissions/5dc21d31-16a1-45a3-9269-7c85e9690b7a

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {m l : ℕ} (h : l ≤ m) (f : Fin m → ℂ)
    (hf : ∀ j : Fin m, l ≤ j.val → f j = 0) :
    ∑ j, f j = ∑ j : Fin l, f (Fin.castLE h j) := by
  rw [show (∑ j : Fin l, f (Fin.castLE h j)) = ∑ j ∈ Finset.univ.map (Fin.castLEEmb h), f j from
    (Finset.sum_map Finset.univ (Fin.castLEEmb h) f).symm]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
  by_contra hlt
  push_neg at hlt
  exact hj (Finset.mem_map.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
end Formalism.QuantumDeterminants
