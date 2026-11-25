-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:05.322884+00:00
-- url     : https://prove2.me/submissions/58b1c22b-f8a1-4f3e-a7ee-b9543a6092e6

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
theorem _root_.solution {R : Type} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R) (h : ∀ i j, M i j ∈ S) :
    M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun s _ => ?_
  rw [Units.smul_def]
  exact S.zsmul_mem (S.prod_mem fun i _ => h _ _) _
end Formalism.L2.FormalSeriesBounds.RF
