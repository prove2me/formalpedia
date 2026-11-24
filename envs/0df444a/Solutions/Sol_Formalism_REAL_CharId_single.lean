-- Prove2me | solution 1 for Formalism.REAL.CharId_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:46.459415+00:00
-- url     : https://prove2.me/submissions/fe7e47fe-4a94-4437-a87b-aef10691100c

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (f : Fin n → Module.End ℂ V) (b : Fin n) (v : V) :
    ∑ c, f c ((Pi.single b v : Fin n → V) c) = f b v := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Pi.single_apply, hc]
  · simp
end Formalism.REAL
