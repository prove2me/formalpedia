-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.flatness_iff_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:25.158532+00:00
-- url     : https://prove2.me/submissions/8db93f6d-1580-4b8d-9d4e-0df8196647d5

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
theorem _root_.solution : FlatIff := by
  constructor
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
      a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a17, a18, a19, a20⟩ ⟨a12, a13, a14, a15, a16⟩
      a21 a22 a23 a24 a25 a26
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a17, a18, a19, a20⟩ ⟨a12, a13, a14, a15, a16⟩
      a21 a22 a23 a24 a25 a26
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
      a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26
end Formalism.LFunctionChainParameters.ProjectiveLineModels
