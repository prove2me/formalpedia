-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.kindAll_pl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:28.532789+00:00
-- url     : https://prove2.me/submissions/2b750d37-efc5-4ebc-ba5f-d4f019684705

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll

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
    (kind : ∀ i, Fin (what₂ i) → Knd d) (s : Σ i : Fin K, Fin (what₂ i)) : kindAll pl kind (pl s) = kind s.1 s.2 := by
  unfold kindAll
  have hex : ∃ s', pl s' = pl s := ⟨s, rfl⟩
  rw [dif_pos hex]
  have hc : hex.choose = s := hpl hex.choose_spec
  rw [hc]
end Formalism.L2.FormalSeriesBounds
