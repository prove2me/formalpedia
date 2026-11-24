-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.line_map_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:46.750997+00:00
-- url     : https://prove2.me/submissions/d5cbd126-3c1a-4e01-88ea-008ef9149b53

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
variable (p : ℕ) [Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution (i : Option (ZMod p) × ZMod p) : lineMap K p i ≠ 0 := by
  intro h0
  have h1 : lineMap K p i (Pi.basisFun K (ZMod p) 0) (linePt p i 0) = 0 := by rw [h0]; rfl
  unfold lineMap at h1
  rw [Matrix.toLin_self] at h1
  simp [Finset.sum_apply, ite_apply] at h1
end Formalism.LFunctionChainParameters.ProjectiveLineModels
