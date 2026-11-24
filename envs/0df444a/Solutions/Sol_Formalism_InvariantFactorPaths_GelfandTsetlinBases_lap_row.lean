-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lap_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:55:29.903983+00:00
-- url     : https://prove2.me/submissions/938364a2-bb37-4b08-af42-6735d21e6b38

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorF_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorF_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_emb_succAbove
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sg_emb
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_det_rows_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (m : Matrix (Fin n) (Fin n) R) (I' J : Finset (Fin n)) (a : Fin n) :
    ∑ b ∈ J, ((sg J b : ℤ) : R) * minorF m I' (J.erase b) * m a b =
      if a ∈ I' then 0 else ((sg (insert a I') a : ℤ) : R) * minorF m (insert a I') J := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, I'.card = d := ⟨_, rfl⟩
  by_cases hJ : J.card = d + 1
  · by_cases ha : a ∈ I'
    · rw [if_pos ha]
      have hr : (fun x => (Fin.cons a ⇑(I'.orderEmbOfFin hd) : Fin (d + 1) → Fin n)
          ((0 : Fin (d + 1)).succAbove x)) = I'.orderEmbOfFin hd := by
        funext x
        simp [Fin.succAbove_zero]
      have hexp := det_rows_expand m (Fin.cons a ⇑(I'.orderEmbOfFin hd) : Fin (d + 1) → Fin n) 0 hJ hd hr
      simp only [Fin.cons_zero] at hexp
      rw [← hexp]
      obtain ⟨k, hk⟩ : ∃ k, I'.orderEmbOfFin hd k = a := by
        have : a ∈ Set.range (I'.orderEmbOfFin hd) := by rw [Finset.range_orderEmbOfFin]; exact ha
        exact this
      rw [Matrix.det_zero_of_row_eq (i := 0) (j := k.succ) (Fin.succ_ne_zero k).symm
        (by funext c; simp [hk]), mul_zero]
    · rw [if_neg ha]
      have hcard : (insert a I').card = d + 1 := by rw [Finset.card_insert_of_notMem ha, hd]
      obtain ⟨i, hi⟩ : ∃ i, (insert a I').orderEmbOfFin hcard i = a := by
        have : a ∈ Set.range ((insert a I').orderEmbOfFin hcard) := by
          rw [Finset.range_orderEmbOfFin]; exact Finset.mem_insert_self a I'
        exact this
      have hr := emb_succAbove hcard i (J' := I') (by rw [hi, Finset.erase_insert ha]) hd
      have hexp := det_rows_expand m ((insert a I').orderEmbOfFin hcard) i hJ hd hr
      rw [hi] at hexp
      rw [← hexp]
      have hs := sg_emb hcard i
      rw [hi] at hs
      rw [hs, minorF_eq m hcard hJ]
      push_cast
      ring
  · rw [Finset.sum_eq_zero]
    · split_ifs with ha
      · rfl
      · rw [minorF_ne, mul_zero]
        rw [Finset.card_insert_of_notMem ha, hd]
        exact hJ
    · intro b hb
      rw [minorF_ne, mul_zero, zero_mul]
      rw [Finset.card_erase_of_mem hb, hd]
      have := Finset.card_pos.mpr ⟨b, hb⟩
      omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
