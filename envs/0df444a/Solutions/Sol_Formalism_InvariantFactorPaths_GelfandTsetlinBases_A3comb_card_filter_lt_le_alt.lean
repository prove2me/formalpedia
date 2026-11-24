-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.card_filter_lt_le_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:44.866328+00:00
-- url     : https://prove2.me/submissions/04077ecc-1805-46da-9f76-09091e3af3e8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
theorem _root_.solution {n : ℕ} (J : Finset (Fin n)) (h j : ℕ) (hJ : J.card = ((rowsLt n h)ᶜ).card) :
    ((rowsLt n j).filter fun m => m ∈ (rowsLt n h)ᶜ).card ≤ ((rowsLt n j).filter fun m => m ∈ J).card := by
  have f1 : ((rowsLt n j).filter fun m => m ∈ (rowsLt n h)ᶜ) = rowsLt n j ∩ (rowsLt n h)ᶜ := by
    ext m
    simp
  have f2 : ((rowsLt n j).filter fun m => m ∈ J) = rowsLt n j ∩ J := by
    ext m
    simp
  rw [f1, f2]
  rcases le_total j h with hjh | hjh
  · have e : rowsLt n j ∩ (rowsLt n h)ᶜ = ∅ := by
      ext m
      constructor
      · intro hm
        simp only [rowsLt, Finset.mem_inter, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
          true_and] at hm
        exact absurd hm (by omega)
      · intro hm
        simp at hm
    rw [e, Finset.card_empty]
    exact Nat.zero_le _
  · have hu : rowsLt n j ∪ (rowsLt n h)ᶜ = univ := by
      ext m
      simp only [rowsLt, Finset.mem_union, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      omega
    have e1 := Finset.card_union_add_card_inter (rowsLt n j) ((rowsLt n h)ᶜ)
    have e2 := Finset.card_union_add_card_inter (rowsLt n j) J
    have e3 := Finset.card_le_univ (rowsLt n j ∪ J)
    rw [hu, Finset.card_univ, Fintype.card_fin] at e1
    rw [Fintype.card_fin] at e3
    omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
