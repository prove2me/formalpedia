-- Prove2me | solution 1 for Formalism.L2.Col.atW_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:37.600056+00:00
-- url     : https://prove2.me/submissions/d9638ea3-019a-4d1d-bedb-0ea953125ce7

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) :
    (atW w L).restrictScalars (𝓞 K) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
  ext x
  rw [Submodule.restrictScalars_mem, mem_atW_iff]
  rfl
end Formalism.L2.Col
