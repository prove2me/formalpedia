-- Prove2me | solution 1 for Formalism.L2.Col.span_atW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:19.737832+00:00
-- url     : https://prove2.me/submissions/4d5f004c-637b-45c5-b760-2ee015ed8b7b

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_le_atW

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Submodule.span K (atW w L : Set V) = Submodule.span K (L : Set V) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    have : atW w L ≤ (Submodule.span K (L : Set V)).restrictScalars (Ow w) :=
      Submodule.span_le.2 Submodule.subset_span
    exact this
  · exact Submodule.span_mono (le_atW w L)
end Formalism.L2.Col
