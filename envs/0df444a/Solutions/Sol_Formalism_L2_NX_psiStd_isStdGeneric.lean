-- Prove2me | solution 1 for Formalism.L2.NX.psiStd_isStdGeneric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:32.518746+00:00
-- url     : https://prove2.me/submissions/7db14375-4ecf-45e5-8707-bfdd365ed39b

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
variable (r)
variable {r}
variable (p r)
namespace Formalism.L2.NX
theorem _root_.solution {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hθ : ∀ x, θ x ≠ 1) :
    IsStdGeneric p r (psiStd p r θ) := ⟨θ, fun _ => hθ, fun _ => rfl⟩
end Formalism.L2.NX
