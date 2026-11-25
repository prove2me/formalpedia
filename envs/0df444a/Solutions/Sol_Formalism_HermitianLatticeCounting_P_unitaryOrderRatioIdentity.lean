-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.unitaryOrderRatioIdentity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:51.145219+00:00
-- url     : https://prove2.me/submissions/c1166614-e808-4fa1-8e39-6f61337c252c

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Icc_eq_Ico_add_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ThetaRatio := by
  intro j e η q hej hq
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.theta
  obtain ⟨m, rfl⟩ : ∃ m, j = m + e := ⟨j - e, by omega⟩
  have hm : m + e - e = m := by omega
  rw [hm]
  simp only [Icc_eq_Ico_add_one]
  rw [← Finset.prod_Ico_consecutive _ (show 1 ≤ m + 1 by omega)
    (show m + 1 ≤ m + e + 1 by omega)]
  ring
end Formalism.HermitianLatticeCounting.P
