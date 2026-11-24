-- Prove2me | solution 1 for Formalism.LT.PadicP.ltLog_subst_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:52.772108+00:00
-- url     : https://prove2.me/submissions/8938bea4-3ee0-43ce-be6f-6cd7abe41667

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Theorems.Thm_Formalism_LT_PadicP_ltLog_funEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.LT.PadicP
theorem _root_.solution :
    (ltLog p).subst ((X : PowerSeries ℚ_[p]) ^ p) = (p : ℚ_[p]) • (ltLog p - X) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h := congrArg (fun t => (p : ℚ_[p]) • t) (ltLog_funEq (p := p))
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hp0, one_smul] at h
  rw [smul_sub, ← h]
  abel
end Formalism.LT.PadicP
