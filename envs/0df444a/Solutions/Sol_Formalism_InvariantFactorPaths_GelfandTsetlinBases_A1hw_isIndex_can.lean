-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.isIndex_can
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:36.62137+00:00
-- url     : https://prove2.me/submissions/d594c532-bf2e-42be-b3ad-caaa9a4e9062

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
theorem _root_.solution {n : ℕ} (μN : Fin n → ℤ) : IsIndex μN (canIdx μN) := by
  intro c
  have hn := Paths.colHeight_le μN c
  unfold canIdx
  split_ifs with hc
  · have : (univ.filter fun m : Fin n => m.val < colHeight μN c) =
        (Finset.range (colHeight μN c)).attachFin (fun i hi => by
          rw [Finset.mem_range] at hi; omega) := by
      ext m; simp
    rw [this, Finset.card_attachFin, Finset.card_range]
  · have h1 : (univ.filter fun m : Fin n => colHeight μN c ≤ m.val) =
        (univ.filter fun m : Fin n => m.val < colHeight μN c)ᶜ := by
      ext m; simp
    have h2 : (univ.filter fun m : Fin n => m.val < colHeight μN c) =
        (Finset.range (colHeight μN c)).attachFin (fun i hi => by
          rw [Finset.mem_range] at hi; omega) := by
      ext m; simp
    rw [h1, Finset.card_compl, h2, Finset.card_attachFin, Finset.card_range, Fintype.card_fin]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw
