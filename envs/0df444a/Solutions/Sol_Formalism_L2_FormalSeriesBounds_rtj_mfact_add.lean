-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_mfact_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:32.895278+00:00
-- url     : https://prove2.me/submissions/2077d204-829a-4103-8187-b08092bc1216

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
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {a b : σ →₀ ℕ} (h : Disjoint a.support b.support) :
    mfact (a + b) = mfact a * mfact b := by
  unfold mfact
  exact Finsupp.prod_add_index_of_disjoint h (fun (_ : σ) (k : ℕ) => k.factorial)
end Formalism.L2.FormalSeriesBounds
