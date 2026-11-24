-- Prove2me | solution 1 for Formalism.L2.NX.mem_Uup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:10.35501+00:00
-- url     : https://prove2.me/submissions/13670277-0d6b-4232-bbff-01107e60e977

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)
variable {r}
variable (r)
variable {p r}
namespace Formalism.L2.NX
theorem _root_.solution {g : GProd p r} : g ∈ Uup p r ↔
    ∀ x, IsUniTri r ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) := Iff.rfl
end Formalism.L2.NX
