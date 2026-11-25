-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_rename_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:38.399008+00:00
-- url     : https://prove2.me/submissions/9e441a6a-5f90-4670-943b-3a3ce994d13c

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
theorem _root_.solution (e : σ ↪ τ) (P : MvPolynomial σ K) :
    MvPolynomial.rename e P ∈ MvPolynomial.supported K (Set.range e) := by
  rw [MvPolynomial.mem_supported]
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename (⇑e) P hi)
  exact ⟨j, rfl⟩
end Formalism.L2.FormalSeriesBounds
