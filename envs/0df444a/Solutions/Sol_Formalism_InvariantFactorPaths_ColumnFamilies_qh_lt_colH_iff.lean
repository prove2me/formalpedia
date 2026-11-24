-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_lt_colH_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:23.730654+00:00
-- url     : https://prove2.me/submissions/583de8a2-2c67-41b7-b28a-a222b1f6ecb5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      exact (not_le.mpr hc) (hm.2.trans (hmu hmt))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega
  · intro h
    have hsub : Finset.Iic t ⊆ (univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ m, h.trans (hmu hm)⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
end Formalism.InvariantFactorPaths.ColumnFamilies
