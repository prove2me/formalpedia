-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_valOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:35.926371+00:00
-- url     : https://prove2.me/submissions/2e8463a9-615b-47af-b7d0-83ba6d9916e5

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
theorem _root_.solution (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) {M : ℕ}
    (P : MvPolynomial (Fin M × WV I) C) (kind : Fin M → Knd d) (gr : Fin M → MvPowerSeries (WV I) C) :
    ValOf hL P kind gr =
      jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ (rtjH hL (kind ρ))))) := by
  unfold ValOf
  refine congrArg (jetAt0 P) (Finset.prod_congr rfl fun ρ _ => ?_)
  rcases kind ρ with _ | ⟨g, a, a'⟩ <;> rfl
end Formalism.L2.FormalSeriesBounds
