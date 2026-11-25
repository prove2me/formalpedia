-- Prove2me | solution 1 for Formalism.BasicNotions.Host.condN_le_four_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:22:16.295918+00:00
-- url     : https://prove2.me/submissions/0c8812d7-e0a0-4a32-a642-054887401875

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_halfSupp
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondRd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_HalfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal
open scoped Pointwise
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
namespace Formalism.BasicNotions.Host
theorem _root_.solution : ((H.QS : ℝ) * H.q * H.d) ≤ 4 * (R.n : ℝ) ^ 2 * H.q * H.d := by
  have h : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le
  have h0 : (0 : ℝ) ≤ (R.n : ℝ) ^ 2 := by positivity
  gcongr
  linarith
end Formalism.BasicNotions.Host
