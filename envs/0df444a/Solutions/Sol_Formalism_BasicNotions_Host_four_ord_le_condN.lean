-- Prove2me | solution 1 for Formalism.BasicNotions.Host.four_ord_le_condN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:20.893505+00:00
-- url     : https://prove2.me/submissions/7e0a3136-ed8d-48af-88f7-5339bba1e99c

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_halfSupp
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondRd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_HalfNorm
import Theorems.Thm_UpperTheory_HF_cond_rd
import Theorems.Thm_UpperTheory_HF_ram_eq


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
theorem _root_.solution : 4 * R.toFrame.ord ≤ H.QS * H.q * H.d := by
  have h := UpperTheory.HF.cond_rd H.toHostAx
  have h2 := UpperTheory.HF.ram_eq H.toHostAx
  refine h.2.2.2.2.2.2.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero) ?_)
  rw [h2.2.2.2.1]
  refine Nat.mul_dvd_mul_right (Nat.mul_dvd_mul h2.2.2.2.2.1 ?_) _
  split_ifs
  exacts [dvd_rfl, one_dvd _]
end Formalism.BasicNotions.Host
