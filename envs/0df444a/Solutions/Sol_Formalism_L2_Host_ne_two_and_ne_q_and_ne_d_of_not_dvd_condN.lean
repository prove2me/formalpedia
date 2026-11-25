-- Prove2me | solution 1 for Formalism.L2.Host.ne_two_and_ne_q_and_ne_d_of_not_dvd_condN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:44.431513+00:00
-- url     : https://prove2.me/submissions/e8f224d0-5213-46d1-8881-793d47b444b4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RamificationIdxEqOneOfNotDvd
import Theorems.Thm_Formalism_HC_HostRaw_two_dvd_QS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Ideal
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.BasicNotions Formalism.FrobeniusOrbits
variable {R : Ranks} (H : Formalism.BasicNotions.Host R)
namespace Formalism.L2.Host
theorem _root_.solution (p : ℕ) (hnd : ¬ p ∣ H.condN) : p ≠ 2 ∧ p ≠ H.q ∧ p ≠ H.d := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact hnd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left H.two_dvd_QS _) _)
  · rintro rfl
    exact hnd (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  · rintro rfl
    exact hnd (dvd_mul_left _ _)
end Formalism.L2.Host
