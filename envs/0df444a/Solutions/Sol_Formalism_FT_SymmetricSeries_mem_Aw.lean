-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.mem_Aw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:29.589728+00:00
-- url     : https://prove2.me/submissions/9f9f1bcf-11d8-44d4-8898-65b7bedd2f1a

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

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
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (m : ℕ) (α : Fin n →₀ ℕ) : α ∈ Aw n m ↔ wt α = m := by
  unfold Aw
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨∑ j, α j, ?_, ?_⟩, h⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff, ← h]
      unfold wt
      exact Finset.sum_le_sum fun j _ => Nat.le_mul_of_pos_left _ (by omega)
    · rw [Finset.mem_finsuppAntidiag]
      exact ⟨rfl, Finset.subset_univ _⟩
end Formalism.FT.SymmetricSeries
