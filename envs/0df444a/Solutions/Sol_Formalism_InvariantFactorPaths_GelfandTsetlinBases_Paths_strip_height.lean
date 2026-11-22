-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.strip_height
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:33:55.296613+00:00
-- url     : https://prove2.me/submissions/218436ec-1577-4984-a8b2-7b985af3dc49

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_le_iff_lt_colHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_le

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
    (hs : HStrip ν μ b) (c : ℤ) :
    colHeight ν c = colHeight μ c ∨ colHeight ν c = colHeight μ c + 1 := by
  obtain ⟨h1, h2, -⟩ := hs
  have l1 : colHeight μ c ≤ colHeight ν c := by
    by_contra hlt
    have hn := colHeight_le μ c
    have hm : (⟨colHeight ν c, by omega⟩ : Fin n).val < colHeight μ c := by
      show colHeight ν c < colHeight μ c
      omega
    have := (le_iff_lt_colHeight hν c _).1 (((le_iff_lt_colHeight hμ c _).2 hm).trans (h1 _))
    exact absurd this (lt_irrefl _)
  have l2 : colHeight ν c ≤ colHeight μ c + 1 := by
    by_contra hlt
    have hn := colHeight_le ν c
    have hm : (⟨colHeight μ c + 1, by omega⟩ : Fin n).val < colHeight ν c := by
      show colHeight μ c + 1 < colHeight ν c
      omega
    have := (le_iff_lt_colHeight hμ c _).1 (((le_iff_lt_colHeight hν c _).2 hm).trans
      (h2 ⟨colHeight μ c, by omega⟩ _ rfl))
    exact absurd this (lt_irrefl _)
  omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
