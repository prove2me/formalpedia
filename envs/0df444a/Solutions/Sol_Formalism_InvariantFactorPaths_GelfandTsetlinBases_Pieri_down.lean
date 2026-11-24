-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:05.570134+00:00
-- url     : https://prove2.me/submissions/0db46c55-e902-4353-9598-842925be7cdf

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_stripsUp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_stripsDown
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_up
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_star_star
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_antitone_star
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_dGT_star
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_HStrip_star

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
theorem _root_.solution (n : ℕ) (μ : Fin n → ℤ) (b : ℕ) (hμ : Antitone μ) :
    ∑ ν ∈ stripsDown μ b, dGT n ν = dGT n μ * (n + b - 1).choose b := by
  rw [← dGT_star n μ, ← up n (star μ) b (antitone_star hμ)]
  refine Finset.sum_nbij' star star (fun ν hν => ?_) (fun ν hν => ?_)
    (fun ν _ => star_star ν) (fun ν _ => star_star ν) (fun ν _ => (dGT_star n ν).symm)
  · rw [mem_stripsDown] at hν
    rw [mem_stripsUp]
    exact HStrip_star hν
  · rw [mem_stripsUp] at hν
    rw [mem_stripsDown]
    simpa only [star_star] using HStrip_star hν
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
