-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_degree_embDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:21.217019+00:00
-- url     : https://prove2.me/submissions/1e152f6b-a074-4022-adf9-050bcafa9c15

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
theorem _root_.solution (e : σ ↪ τ) (μ : σ →₀ ℕ) : (Finsupp.embDomain e μ).degree = μ.degree := by
  simp only [Finsupp.degree]
  exact Finsupp.sum_embDomain (g := fun (_ : τ) (k : ℕ) => k)
end Formalism.L2.FormalSeriesBounds
