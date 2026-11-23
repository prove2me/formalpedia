-- Prove2me | solution 1 for Formalism.L2.Col.atW_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:55.151771+00:00
-- url     : https://prove2.me/submissions/cb591dde-fe22-44d1-981d-5b96454fba3a

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} (h : A ≤ B) :
    atW w A ≤ atW w B := Submodule.span_mono h
end Formalism.L2.Col
