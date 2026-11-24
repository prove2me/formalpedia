-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.power_hyp_to_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:50.494959+00:00
-- url     : https://prove2.me/submissions/2a6a5cd5-d4ca-495c-81d6-93551026130e

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
theorem _root_.solution : HypPowToRam := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr
    s u U HH δ Dstar η0 η1 e0 de bb x c
  rintro ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hinv : x ^ (-c) = (x ^ c)⁻¹ := Real.rpow_neg hx0.le c
  refine ⟨a0, a1, a2, a3, a4, a5, Real.rpow_pos_of_pos hx0 _, a6, ?_, a8, a9, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, ?_, a19, a20, a21⟩
  · rw [hinv, div_inv_eq_mul]; exact a7
  · rw [hinv, div_inv_eq_mul, mul_comm]; exact a19
end Formalism.LFunctionChainParameters.ProjectiveLineModels
