-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.shape_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.860314+00:00
-- url     : https://prove2.me/submissions/b76725de-8e11-4238-a1a9-18de306040be

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Branch
private theorem le_iff_lt_colHeight_of_antitone {n : ℕ} {κ : Fin n → ℤ} (h : Antitone κ) (c : ℤ) (i : Fin n) :
    c ≤ κ i ↔ i.val < colHeight κ c := by
  unfold colHeight
  constructor
  · intro hc
    have hsub : Finset.Iic i ⊆ univ.filter fun m => c ≤ κ m := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans hc (h hm)
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h1
    omega
  · intro hi
    by_contra hc
    have hsub : (univ.filter fun m => c ≤ κ m) ⊆ Finset.Iio i := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_Iio]
      by_contra hmi
      push_neg at hmi
      exact hc (le_trans hm (h hmi))
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h1
    omega
end Branch
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
theorem _root_.solution {n : ℕ} {κ κ' : Fin n → ℤ} (h : Antitone κ) (h' : Antitone κ')
    (he : ∀ c, colHeight κ c = colHeight κ' c) : κ = κ' := by
  funext i
  apply le_antisymm
  · rw [le_iff_lt_colHeight_of_antitone h' (κ i) i, ← he, ← le_iff_lt_colHeight_of_antitone h]
  · rw [le_iff_lt_colHeight_of_antitone h (κ' i) i, he, ← le_iff_lt_colHeight_of_antitone h']
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
