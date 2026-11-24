-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.local_length_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:49.633552+00:00
-- url     : https://prove2.me/submissions/475f1ab3-b462-410c-9389-89a2b2b510fa

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ProjectiveLineModels
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (w : slopeLatticeData.FinPl K) (L : Submodule (𝓞 K) V) : slopeLatticeData.lenAt w L L = 0 := by
  have := w.2.isPrime
  have hs : Subsingleton (L ⧸ L.comap L.subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_self]
  unfold slopeLatticeData.lenAt
  rw [Module.length_eq_zero_iff]
  infer_instance
end Formalism.LFunctionChainParameters.ProjectiveLineModels
