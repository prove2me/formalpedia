-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_rename_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:37.229379+00:00
-- url     : https://prove2.me/submissions/4d031ce0-ded2-4438-853f-ab553e858964

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
theorem _root_.solution {α β : Type} {f g : α → β} [Filter.TendstoCofinite f] [Filter.TendstoCofinite g]
    (h : f = g) (p : MvPowerSeries α C) : MvPowerSeries.rename f p = MvPowerSeries.rename g p := by
  subst h
  rfl
end Formalism.L2.FormalSeriesBounds
