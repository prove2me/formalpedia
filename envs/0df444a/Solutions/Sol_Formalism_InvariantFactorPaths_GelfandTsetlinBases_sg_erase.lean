-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg_erase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.647053+00:00
-- url     : https://prove2.me/submissions/6e437b92-09ea-4580-86be-9b38bf48d466

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
theorem _root_.solution {I : Finset (Fin n)} {m' : Fin n} (hm' : m' ∈ I) (m : Fin n) :
    sg (I.erase m') m = sg I m * (if m < m' then -1 else 1) := by
  unfold sg
  rw [Finset.filter_erase]
  split_ifs with h
  · have hmem : m' ∈ I.filter (fun j => m < j) := Finset.mem_filter.mpr ⟨hm', h⟩
    rw [Finset.card_erase_of_mem hmem]
    obtain ⟨c, hc⟩ : ∃ c, (I.filter fun j => m < j).card = c + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨m', hmem⟩)).symm⟩
    rw [hc, Nat.add_sub_cancel, pow_succ]
    ring
  · rw [Finset.erase_eq_of_notMem (fun hmem => h (Finset.mem_filter.mp hmem).2), mul_one]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
