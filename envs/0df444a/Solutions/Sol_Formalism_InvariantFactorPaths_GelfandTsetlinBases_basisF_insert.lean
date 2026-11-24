-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.basisF_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.716122+00:00
-- url     : https://prove2.me/submissions/89ec2d61-1ec9-4e7f-a7ee-c1233f8dd487

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract

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
theorem _root_.solution {a : Fin n} {s : Finset (Fin n)} (hs : ∀ x ∈ s, x < a) :
    (basisF (insert a s) : Form R n) = wedgeF (basisF s) (Pi.single a 1) := by
  have has : a ∉ s := fun h => lt_irrefl a (hs a h)
  have hsg : sg (insert a s) a = 1 := by
    unfold sg
    have : (insert a s).filter (fun j => a < j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact lt_irrefl _
      · exact lt_asymm (hs x hx)
    rw [this]
    rfl
  funext I
  simp only [wedgeF, basisF, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq]
  by_cases ha : a ∈ I
  · rw [if_pos ha]
    by_cases hI : I = insert a s
    · subst hI
      rw [if_pos rfl, Finset.erase_insert has, if_pos rfl, hsg]
      simp
    · have : I.erase a ≠ s := fun he => hI (by rw [← he, Finset.insert_erase ha])
      rw [if_neg hI, if_neg this]
  · rw [if_neg ha, if_neg]
    rintro rfl
    exact ha (Finset.mem_insert_self a s)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
