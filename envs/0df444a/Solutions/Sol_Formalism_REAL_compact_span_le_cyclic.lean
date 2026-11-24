-- Prove2me | solution 1 for Formalism.REAL.compact_span_le_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:05.790841+00:00
-- url     : https://prove2.me/submissions/d4f6b180-caa7-4767-8178-0c527b329a44

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_mem_cyclic_self
import Theorems.Thm_Formalism_REAL_cyclic_submodule_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution : kSpan ε E u ≤ cyc E u := by
  unfold kSpan
  apply sInf_le
  refine ⟨mem_cyclic_self E u, ?_⟩
  intro a b _ x hx
  exact cyclic_submodule_stable E u a b x hx
end Formalism.REAL
