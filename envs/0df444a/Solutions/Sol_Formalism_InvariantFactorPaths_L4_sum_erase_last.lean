-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.sum_erase_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:53.325533+00:00
-- url     : https://prove2.me/submissions/1755f2d4-14f4-46fd-9e60-13edb56eeee5

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {r : ℕ} (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (G : ℕ → ℤ) :
    ∑ a ∈ univ.erase ρ, G (a : ℕ) = ∑ i ∈ range (r - 1), G i := by
  have hr : r - 1 + 1 = r := by have := ρ.isLt; omega
  have h1 : ∑ a : Fin r, G (a : ℕ) = ∑ i ∈ range r, G i := Fin.sum_univ_eq_sum_range G r
  have h2 : ∑ i ∈ range r, G i = ∑ i ∈ range (r - 1), G i + G (r - 1) := by
    rw [← Finset.sum_range_succ, hr]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), h2, hρ] at h1
  linarith
end Formalism.InvariantFactorPaths.L4
