-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.modCond_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:07.224808+00:00
-- url     : https://prove2.me/submissions/03b84593-9f56-4d3b-9365-e0cdec57fb3d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)
variable (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (f g : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : ModCond p LL j M f)
    (hg : ModCond p LL j M g) : ModCond p LL j M (f + g) := by
  intro l hl m hm
  rw [map_add, coeff_add]
  exact lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt (hf l hl m hm) (hg l hl m hm))
end Formalism.InvariantFactorPaths.L4
