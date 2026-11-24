-- Prove2me | solution 1 for Formalism.REAL.CharId_P_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:41.4688+00:00
-- url     : https://prove2.me/submissions/cc098777-fe25-4d7a-960e-022c2d7d6837

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
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (a b : Fin n) (x : V) :
    CharId_P E ν a b x = ∑ i ∈ range (n + 1),
      (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b x := by
  simp [CharId_P]
end Formalism.REAL
