-- Prove2me | solution 1 for Formalism.L2.Col.mem_scalW_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:20.432704+00:00
-- url     : https://prove2.me/submissions/f36b232d-546e-495c-b16b-9d1e2c9ec325

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {c : K} {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ scalW w c L ↔ ∃ y ∈ atW w L, c • y = x := Iff.rfl
end Formalism.L2.Col
