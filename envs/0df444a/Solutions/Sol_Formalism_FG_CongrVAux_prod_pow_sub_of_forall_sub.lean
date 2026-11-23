-- Prove2me | solution 1 for Formalism.FG.CongrVAux.prod_pow_sub_of_forall_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:39.492641+00:00
-- url     : https://prove2.me/submissions/cd43434e-de3c-4a3f-841e-181ae5055d1b

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_FG_CongrVAux_zd_zero
import Theorems.Thm_Formalism_FG_CongrVAux_zd_mul_sub
import Theorems.Thm_Formalism_FG_SolveVAux_P_add
import Theorems.Thm_Formalism_FG_SolveVAux_P_single
import Theorems.Thm_Formalism_FG_SolveVAux_P_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {ι : Type v} {d : τ →₀ ℕ} {k k' : ι → MvPowerSeries τ R}
    (hkk : ∀ i, Zd d (k i - k' i)) (e : ι →₀ ℕ) : Zd d (P k e - P k' e) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [P_zero, P_zero, sub_self]; exact zd_zero _
  | add e₁ e₂ h₁ h₂ =>
    rw [P_add, P_add]; exact zd_mul_sub h₁ h₂
  | single i n =>
    rw [P_single, P_single]
    induction n with
    | zero => rw [pow_zero, pow_zero, sub_self]; exact zd_zero _
    | succ n ih => rw [pow_succ, pow_succ]; exact zd_mul_sub ih (hkk i)
end Formalism.FG.CongrVAux
