-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_laplace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:33:04.075337+00:00
-- url     : https://prove2.me/submissions/73138f83-56e6-48c1-9475-bb4415ed8cbe

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_oe_succAbove
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_gt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_lap_row

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
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (A I : Finset (Fin n)) (k : Fin n) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g k m =
      if k ∈ A then 0 else ((qs_sg A k : ℤ) : R) * qs_mn g (insert k A) I := by
  by_cases hc : I.card = A.card + 1
  · split_ifs with hk
    ·
      have hk' : k ∈ Set.range (A.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hk
      obtain ⟨q, hq⟩ := hk'
      have := qs_lap_row g (Fin.cons k (A.orderEmbOfFin rfl)) 0 I hc A rfl (fun i => by simp)
      simp only [Fin.cons_zero] at this
      rw [this, Matrix.det_zero_of_row_eq (i := 0) (j := q.succ) (Fin.succ_ne_zero q).symm, mul_zero]
      ext b; simp [hq]
    · have hs : (insert k A).card = A.card + 1 := Finset.card_insert_of_notMem hk
      have hk' : k ∈ Set.range ((insert k A).orderEmbOfFin hs) := by
        rw [Finset.range_orderEmbOfFin]; simp
      obtain ⟨p, hp⟩ := hk'
      have he : (insert k A).erase ((insert k A).orderEmbOfFin hs p) = A := by
        rw [hp, Finset.erase_insert hk]
      have hAc : ((insert k A).erase ((insert k A).orderEmbOfFin hs p)).card = A.card := by rw [he]
      have := qs_lap_row g ((insert k A).orderEmbOfFin hs) p I hc _ hAc
        (fun i => qs_oe_succAbove _ hs p hAc i)
      have h2 := qs_card_gt (insert k A) hs p
      rw [he, hp] at this h2
      rw [this, qs_mn_eq g _ _ hs hc, qs_sg, h2]
      push_cast; rfl
  · have h1 : ∀ m ∈ I, qs_mn g A (I.erase m) = 0 := fun m hm => qs_mn_ne g (by
      rw [Finset.card_erase_of_mem hm]
      have := Finset.card_pos.2 ⟨m, hm⟩
      omega)
    rw [Finset.sum_eq_zero (fun m hm => by rw [h1 m hm]; simp)]
    split_ifs with hk
    · rfl
    · rw [qs_mn_ne g (by rw [Finset.card_insert_of_notMem hk]; omega), mul_zero]
end Formalism.InvariantFactorPaths.ColumnFamilies
