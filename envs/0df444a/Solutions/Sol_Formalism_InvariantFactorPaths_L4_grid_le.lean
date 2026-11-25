-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.grid_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:38.522749+00:00
-- url     : https://prove2.me/submissions/265945cc-3257-498e-882f-4046c6858a88

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {N : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (T : TieData) (Yl n₀ dd : Fin T.t → ℕ) (n : Fin T.t → ℕ)
    (hn : n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))) :
    ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1) := by
  intro i
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 (Fintype.mem_piFinset.1 hn i)
  rw [← hji]
  have hj' : j ≤ Yl i - 1 := by
    have := Finset.mem_range.1 hj
    omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hj') _
end Formalism.InvariantFactorPaths.L4
