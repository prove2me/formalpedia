-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.reg_Dop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:44.121569+00:00
-- url     : https://prove2.me/submissions/a2bf893e-c007-45dd-80fe-7ad00fa4fe88

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_contDiffAt_Wc
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_fun
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirtBar_fun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution {g : (Fin m → ℂ) → E} (hg : Reg g) (k : Fin m) (j : Fin 6) : Reg (Dop k j g) := by
  intro x hx
  match j with
  | 0 =>
    show ContDiffAt ℝ ∞ (wirt k g) x
    rw [wirt_fun]
    exact contDiffAt_Wc (hg x hx) _ _ _
  | 1 => exact hg x hx
  | 2 => exact hg x hx
  | 3 =>
    show ContDiffAt ℝ ∞ (wirtBar k g) x
    rw [wirtBar_fun]
    exact contDiffAt_Wc (hg x hx) _ _ _
  | 4 => exact hg x hx
  | 5 => exact hg x hx
end Formalism.QuantumDeterminants.WirtingerDerivatives
