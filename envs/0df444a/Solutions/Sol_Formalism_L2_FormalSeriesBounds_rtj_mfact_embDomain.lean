-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_mfact_embDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:35.084159+00:00
-- url     : https://prove2.me/submissions/47ad3bee-3017-488d-8b90-04a58b082788

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
variable {K : Type} [Field K] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (e : σ ↪ τ) (m : σ →₀ ℕ) : mfact (Finsupp.embDomain e m) = mfact m := by
  unfold mfact
  exact Finsupp.prod_embDomain (g := fun (_ : τ) (k : ℕ) => k.factorial)
end Formalism.L2.FormalSeriesBounds
