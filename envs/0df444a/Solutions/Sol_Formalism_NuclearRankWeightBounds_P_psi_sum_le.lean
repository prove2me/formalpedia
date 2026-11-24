-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.psi_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:02.76889+00:00
-- url     : https://prove2.me/submissions/d853ccdc-28f5-4e85-8745-7bdfa6da1645

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_psi_nonneg
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_summable_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution (T : Finset ℤ) : ∑ n ∈ T, psi n ≤ ∑' n, psi n :=
  summable_psi.sum_le_tsum T (fun n _ => psi_nonneg n)
end Formalism.NuclearRankWeightBounds.P
