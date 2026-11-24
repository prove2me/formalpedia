-- Prove2me | solution 1 for Formalism.LT.CoeffP.powpj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:50.435733+00:00
-- url     : https://prove2.me/submissions/a21f7aa9-dd17-4a87-91c1-1ef7deb9b65f

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Theorems.Thm_Formalism_LT_CoeffP_Bd_pow
import Theorems.Thm_Formalism_LT_CoeffP_powp_step

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
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
namespace Formalism.LT.CoeffP
theorem _root_.solution {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) (A - B)) :
    ∀ j : ℕ, Bd (‖(p : K)‖ ^ (r + j)) (A ^ (p ^ j) - B ^ (p ^ j))
  | 0 => by simpa using hD
  | j + 1 => by
    rw [pow_succ p j, pow_mul, pow_mul, ← add_assoc]
    exact powp_step hp (by omega) (by simpa using hA.pow zero_le_one (p ^ j))
      (by simpa using hB.pow zero_le_one (p ^ j)) (solution hp hr hA hB hD j)
end Formalism.LT.CoeffP
