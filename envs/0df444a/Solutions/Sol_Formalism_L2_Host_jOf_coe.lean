-- Prove2me | solution 1 for Formalism.L2.Host.jOf_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:36:24.568799+00:00
-- url     : https://prove2.me/submissions/06057af5-70e7-41d6-91be-d0ec810e3ba2

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.L2.Host
theorem _root_.solution (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) (x : hostE ζ a b) :
    ((jOf h f x : EQ e q d) : Qb) = f x := rfl
end Formalism.L2.Host
