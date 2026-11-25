-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.b_ramified_grouped_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:28.091382+00:00
-- url     : https://prove2.me/submissions/4bdeceb1-86f0-4354-af3c-20b39a186e72

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
theorem _root_.solution : BRamGrouped := by
  constructor
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      s u U HH δ Dstar sg η0 η1 e0 de bb x c
    rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23⟩
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      s u U HH δ Dstar sg η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
  · intro H K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
      s u U HH δ Dstar sg η0 η1 e0 de bb x c
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
    exact H K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ ιf Bf Vr
      s u U HH δ Dstar sg η0 η1 e0 de bb x c
      ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23⟩
end Formalism.LFunctionChainParameters.ProjectiveLineModels
