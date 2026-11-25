-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_rowCopy_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:26:30.194828+00:00
-- url     : https://prove2.me/submissions/9e8bb59e-0d58-4403-8208-6ac50ffb2a8a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {M : ℕ} (ρ : Fin M) (F : MvPowerSeries (WV I) C) :
    rowCopy ρ F = MvPowerSeries.rename (rtjR ρ) F := by
  unfold rowCopy
  rw [MvPowerSeries.rename_eq_subst]
  rfl
end Formalism.L2.FormalSeriesBounds
