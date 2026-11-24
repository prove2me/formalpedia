-- Prove2me | solution 1 for Formalism.REAL.twistedAction_mem_tailSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:53.487624+00:00
-- url     : https://prove2.me/submissions/b568aa82-ab06-4d5d-878e-75e021ea882f

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
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (j : ℕ) (c d : Fin n) (y : Fin n → V)
    (hy : y ∈ CharId_F E v j) : twistedAction E c d y ∈ CharId_F E v j := Submodule.mem_sInf.2 fun W hW => hW.2 c d y (Submodule.mem_sInf.1 hy W hW)
end Formalism.REAL
