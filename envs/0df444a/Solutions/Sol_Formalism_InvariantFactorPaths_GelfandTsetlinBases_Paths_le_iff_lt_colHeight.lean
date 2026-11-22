-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.le_iff_lt_colHeight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:20.533822+00:00
-- url     : https://prove2.me/submissions/ef76346a-b93e-496a-87fa-94b7a2b3d4b0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight

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
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
theorem _root_.solution {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) (c : ℤ) (m : Fin n) :
    c ≤ μ m ↔ m.val < colHeight μ c := by
  unfold colHeight
  constructor
  · intro hm
    have hsub : Finset.Iic m ⊆ univ.filter fun m => c ≤ μ m := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and]
      exact hm.trans (h (Finset.mem_Iic.1 hx))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hm
    by_contra hc
    have hsub : (univ.filter fun m => c ≤ μ m) ⊆ Finset.Iio m := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [Finset.mem_Iio]
      by_contra hx'
      exact hc (hx.trans (h (not_lt.1 hx')))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
