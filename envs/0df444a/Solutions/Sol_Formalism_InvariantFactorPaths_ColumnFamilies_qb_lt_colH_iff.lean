-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_lt_colH_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:24.168238+00:00
-- url     : https://prove2.me/submissions/afd4af28-aed9-4b3f-b324-423df7b5f99f

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW

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
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (b : Fin n) :
    b.val < colH mu c ↔ c ≤ mu b := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    have : (univ.filter fun m => c ≤ mu m) ⊆ Finset.Iio b := fun m hm => by
      simp only [mem_filter, mem_univ, true_and] at hm
      rw [mem_Iio]
      by_contra hmb
      exact hc (hm.trans (hmu (not_lt.1 hmb)))
    have := card_le_card this
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have : Finset.Iic b ⊆ (univ.filter fun m => c ≤ mu m) := fun m hm => by
      simp only [mem_filter, mem_univ, true_and]
      exact h.trans (hmu (mem_Iic.1 hm))
    have := card_le_card this
    rw [Fin.card_Iic] at this
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
