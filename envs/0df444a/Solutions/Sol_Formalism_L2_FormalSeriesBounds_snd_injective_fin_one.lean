-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.snd_injective_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:11.079424+00:00
-- url     : https://prove2.me/submissions/79100ceb-0d60-43a7-9d68-8cc4e83a650b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : Function.Injective (fun p : Fin 1 × Fin dd => p.2) := fun p q h => Prod.ext (Subsingleton.elim _ _) h
end Formalism.L2.FormalSeriesBounds
