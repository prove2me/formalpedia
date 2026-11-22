-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_rem_iff_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:36.537748+00:00
-- url     : https://prove2.me/submissions/0975c1e9-2ce8-481a-aab2-1f746cfe81b8

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_not
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_add_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (D : Finset ℤ) (J K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) :
    ((∀ c : ↥D, m c ∈ K c.1) ∧ J = qs_rem D K m) ↔ ((∀ c : ↥D, m c ∉ J c.1) ∧ K = qs_add D J m) := by
  constructor
  · rintro ⟨h1, rfl⟩
    refine ⟨fun c => by rw [qs_rem_mem]; simp, ?_⟩
    funext c
    by_cases hc : c ∈ D
    · have := qs_add_mem D (qs_rem D K m) m ⟨c, hc⟩
      have h2 := qs_rem_mem D K m ⟨c, hc⟩
      simp only at this h2
      rw [this, h2, Finset.insert_erase (h1 ⟨c, hc⟩)]
    · rw [qs_add_not _ _ _ hc, qs_rem_not _ _ _ hc]
  · rintro ⟨h1, rfl⟩
    refine ⟨fun c => by rw [qs_add_mem]; simp, ?_⟩
    funext c
    by_cases hc : c ∈ D
    · have := qs_rem_mem D (qs_add D J m) m ⟨c, hc⟩
      have h2 := qs_add_mem D J m ⟨c, hc⟩
      simp only at this h2
      rw [this, h2, Finset.erase_insert (h1 ⟨c, hc⟩)]
    · rw [qs_rem_not _ _ _ hc, qs_add_not _ _ _ hc]
end Formalism.InvariantFactorPaths.ColumnFamilies
