-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_minor_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:44:34.482088+00:00
-- url     : https://prove2.me/submissions/87d98b49-8e73-438b-868f-8d7a7c3dbca0

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_mem_last

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
variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K : Finset (Fin (m + 1))) (S : Finset (Fin m))
    {k : ℕ} (hK : K.card = k) (hS : (qr_ext e S).card = k) (hne : ¬ (Fin.last m ∈ K ↔ e)) :
    (h.val.submatrix (K.orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det = 0 := by
  by_cases he : e
  · have hl : Fin.last m ∉ K := fun hl => hne ⟨fun _ => he, fun _ => hl⟩
    have h1 : Fin.last m ∈ Set.range ((qr_ext e S).orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact (qr_mem_last e S).2 he
    obtain ⟨b0, hb0⟩ := h1
    apply Matrix.det_eq_zero_of_column_eq_zero b0
    intro a
    rw [Matrix.submatrix_apply, hb0]
    have h2 : K.orderEmbOfFin hK a ≠ Fin.last m := fun h3 => hl (h3 ▸ Finset.orderEmbOfFin_mem K hK a)
    obtain ⟨a', ha'⟩ := Fin.exists_castSucc_eq.2 h2
    rw [← ha']
    exact (hb.2.2 a').1
  · have hl : Fin.last m ∈ K := by
      by_contra hl; exact hne ⟨fun h => absurd h hl, fun h => absurd h he⟩
    have h1 : Fin.last m ∈ Set.range (K.orderEmbOfFin hK) := by
      rw [Finset.range_orderEmbOfFin]; exact hl
    obtain ⟨a0, ha0⟩ := h1
    apply Matrix.det_eq_zero_of_row_eq_zero a0
    intro b
    rw [Matrix.submatrix_apply, ha0]
    have h2 : (qr_ext e S).orderEmbOfFin hS b ≠ Fin.last m := fun h3 =>
      he ((qr_mem_last e S).1 (h3 ▸ Finset.orderEmbOfFin_mem _ hS b))
    obtain ⟨b', hb'⟩ := Fin.exists_castSucc_eq.2 h2
    rw [← hb']
    exact (hb.2.2 b').2
end Formalism.InvariantFactorPaths.ColumnFamilies
