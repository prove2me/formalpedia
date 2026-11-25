-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.rename_mem_ZP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:48:02.428173+00:00
-- url     : https://prove2.me/submissions/7486fcf6-f35c-4311-9853-4f12c25e3f79

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral

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
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {σ τ : Type} (k : σ → τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) :
    MvPolynomial.rename k P ∈ ZP C τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  exact RingHom.mem_range.2 ⟨MvPolynomial.rename k Q, MvPolynomial.map_rename _ _ _⟩
end Formalism.L2.FormalSeriesBounds.RF
