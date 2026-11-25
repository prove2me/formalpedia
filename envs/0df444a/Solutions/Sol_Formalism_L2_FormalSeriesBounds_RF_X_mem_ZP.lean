-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.X_mem_ZP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:15.646834+00:00
-- url     : https://prove2.me/submissions/c39b31cc-10f3-4d81-9041-e980997741cb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution {σ : Type} (x : σ) : (MvPolynomial.X x : MvPolynomial σ C) ∈ ZP C σ :=
  RingHom.mem_range.2 ⟨MvPolynomial.X x, MvPolynomial.map_X _ _⟩
end Formalism.L2.FormalSeriesBounds.RF
