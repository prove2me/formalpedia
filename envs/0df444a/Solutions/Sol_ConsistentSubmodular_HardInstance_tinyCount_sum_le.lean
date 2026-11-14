-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.tinyCount_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:51.638169+00:00
-- url     : https://prove2.me/submissions/b724bfad-3ec1-4f1b-8338-f0a0edcf4d09

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem solution {k : ℕ} (T : Finset (Fin (3 * k + 2))) :
    tinyCount k 0 T + tinyCount k 1 T + tinyCount k 2 T ≤ T.card := by
  have hdisj (g h : Fin 3) (hgh : g ≠ h) :
      Disjoint (T.filter fun e => e.val < 3 * k ∧ e.val / k = g.val)
        (T.filter fun e => e.val < 3 * k ∧ e.val / k = h.val) := by
    rw [disjoint_filter]
    intro e _ hg hh
    exact hgh (Fin.ext (hg.2.symm.trans hh.2))
  unfold tinyCount
  rw [← card_union_of_disjoint (hdisj 0 1 (by decide)),
    ← card_union_of_disjoint (disjoint_union_left.mpr ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩)]
  exact card_le_card (union_subset (union_subset (filter_subset _ _) (filter_subset _ _))
    (filter_subset _ _))

end
