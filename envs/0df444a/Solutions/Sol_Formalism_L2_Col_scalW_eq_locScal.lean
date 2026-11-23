-- Prove2me | solution 1 for Formalism.L2.Col.scalW_eq_locScal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:38.226931+00:00
-- url     : https://prove2.me/submissions/3017ef1d-c75d-431d-8fcb-e9019cd3a25f

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (c : K) (L : Submodule (𝓞 K) V) :
    scalW w c L = @Formalism.LFunctionChainParameters.slopeLatticeData.locScal K V _ _ _ _ _ (plEquiv K w) (owModule w V) c L := by
  unfold scalW atW Formalism.LFunctionChainParameters.slopeLatticeData.locScal
  rw [Submodule.map_span]
  rfl
end Formalism.L2.Col
