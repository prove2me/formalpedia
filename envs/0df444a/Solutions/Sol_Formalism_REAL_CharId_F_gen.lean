-- Prove2me | solution 1 for Formalism.REAL.CharId_F_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:58.513614+00:00
-- url     : https://prove2.me/submissions/f683fdbf-217c-4af7-bc89-c4e734d741b2

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
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (j : ℕ) (t : Fin n) (ht : j ≤ (t : ℕ)) :
    Pi.single t v ∈ CharId_F E v j := Submodule.mem_sInf.2 fun _ hW => hW.1 t ht
end Formalism.REAL
