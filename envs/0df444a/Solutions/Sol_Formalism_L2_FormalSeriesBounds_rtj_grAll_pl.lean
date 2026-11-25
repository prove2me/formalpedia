-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_grAll_pl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:31.802831+00:00
-- url     : https://prove2.me/submissions/4977cf37-7b06-4631-8390-850a1dc3b0a7

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
theorem _root_.solution {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C) (s : Σ i : Fin K, Fin (what₂ i)) :
    grAll pl gr (pl s) = gr s.1 s.2 := by
  unfold grAll
  have h : ∃ s', pl s' = pl s := ⟨s, rfl⟩
  rw [dif_pos h]
  have hs : h.choose = s := hpl h.choose_spec
  rw [hs]
end Formalism.L2.FormalSeriesBounds
