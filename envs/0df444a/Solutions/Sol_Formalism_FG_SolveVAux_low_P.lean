-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:56.211185+00:00
-- url     : https://prove2.me/submissions/bab9bd17-9890-43d9-aa6d-7e6ef7e56461

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_P_add
import Theorems.Thm_Formalism_FG_SolveVAux_P_single
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

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
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) (e : ι →₀ ℕ) :
    Low e.degree (P k e) := by
  induction e using Finsupp.induction_linear with
  | zero => exact low_zero _
  | add e₁ e₂ h₁ h₂ =>
    rw [P_add, map_add]; exact low_mul h₁ h₂
  | single i n =>
    rw [P_single, Finsupp.degree_single]; exact low_pow (hk i) n
end Formalism.FG.SolveVAux
