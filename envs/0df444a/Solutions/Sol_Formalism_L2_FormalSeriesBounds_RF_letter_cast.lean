-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.letter_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:49:18.569373+00:00
-- url     : https://prove2.me/submissions/bcad363f-ea8f-4aec-87bc-914b5f685161

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {T : Type} {r : T → ℕ} {n : ℕ} {σ σ' : T} (h : σ = σ') (a : Fin (r σ)) :
    ∃ a' : Fin (r σ'), ∀ b : Fin n, (⟨σ, a, b⟩ : Letter T r n) = ⟨σ', a', b⟩ := by
  subst h
  exact ⟨a, fun b => rfl⟩
end Formalism.L2.FormalSeriesBounds.RF
