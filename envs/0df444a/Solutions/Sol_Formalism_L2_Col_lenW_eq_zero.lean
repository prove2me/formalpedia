-- Prove2me | solution 1 for Formalism.L2.Col.lenW_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:38.3608+00:00
-- url     : https://prove2.me/submissions/82084168-f0cd-43fb-bb82-dbc30e51ee4d

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} (h : atW w A ≤ atW w B) :
    lenW w A B = 0 := by
  unfold lenW
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro x _
  exact h x.2
end Formalism.L2.Col
