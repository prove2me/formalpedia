-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.changed_ncard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:49.233847+00:00
-- url     : https://prove2.me/submissions/9cc8e7d9-8fdc-4ad3-b729-331ae8a65945

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_le_iff_lt_colHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_strip_height
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_changed_eq

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
theorem _root_.solution {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (hμ : Antitone μ)
    (hs : HStrip ν μ b) : {c : ℤ | colHeight ν c ≠ colHeight μ c}.ncard = b := by
  rw [changed_eq hν hμ hs, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp only [Int.card_Ioc]
    obtain ⟨h1, -, h3⟩ := hs
    have : ((∑ m : Fin n, (ν m - μ m).toNat : ℕ) : ℤ) = (b : ℤ) := by
      push_cast
      rw [← h3, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => Int.toNat_of_nonneg (sub_nonneg.2 (h1 m))
    exact_mod_cast this
  · intro x _ y _ hxy
    show Disjoint (Finset.Ioc (μ x) (ν x)) (Finset.Ioc (μ y) (ν y))
    rw [Finset.disjoint_left]
    intro c hx hy
    rw [Finset.mem_Ioc] at hx hy
    apply hxy
    have hh := strip_height hν hμ hs c
    have a1 := (le_iff_lt_colHeight hν c x).1 hx.2
    have a2 : ¬ x.val < colHeight μ c := fun hlt =>
      absurd ((le_iff_lt_colHeight hμ c x).2 hlt) (not_le.2 hx.1)
    have b1 := (le_iff_lt_colHeight hν c y).1 hy.2
    have b2 : ¬ y.val < colHeight μ c := fun hlt =>
      absurd ((le_iff_lt_colHeight hμ c y).2 hlt) (not_le.2 hy.1)
    exact Fin.ext (by omega)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
