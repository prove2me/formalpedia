-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.standard_lattice_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:48.675596+00:00
-- url     : https://prove2.me/submissions/ad2070f7-2cfa-4a74-9944-ae5d8a97e7cf

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
theorem _root_.solution (K n : Type) [Field K] [NumberField K] [Fintype n] [Nonempty n] :
    stdLat K n ≠ ⊥ := by
  intro h0
  obtain ⟨i⟩ := (inferInstance : Nonempty n)
  have h1 : Pi.basisFun K n i ∈ stdLat K n := Submodule.subset_span ⟨i, rfl⟩
  rw [h0] at h1
  exact (Pi.basisFun K n).ne_zero i ((Submodule.mem_bot _).1 h1)
end Formalism.LFunctionChainParameters.ProjectiveLineModels
