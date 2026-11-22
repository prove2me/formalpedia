-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.standard_lattice_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:37.128946+00:00
-- url     : https://prove2.me/submissions/fa613297-9a62-4975-922e-fb39fc0a27d5

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
theorem _root_.solution (K n : Type) [Field K] [NumberField K] [Fintype n] :
    Submodule.span K ((stdLat K n : Submodule (𝓞 K) (n → K)) : Set (n → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K n).span_eq]
  exact Submodule.span_mono Submodule.subset_span
end Formalism.LFunctionChainParameters.ProjectiveLineModels
