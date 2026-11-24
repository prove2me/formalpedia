-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.hs_Kd_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:40:55.513976+00:00
-- url     : https://prove2.me/submissions/61c8316e-67fe-4316-a5b8-60072ec8678a

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_hilbert_schmidt_unitary_invariant
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Kd_tw_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {ι : Type} [Fintype ι] {D D' : ℕ} {d : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (c : ι → ℂ)
    (V : Matrix (Fin D') (Fin D) ℂ) (U : ∀ u, Matrix (Fin (d u)) (Fin (d u)) ℂ)
    (hc : ∀ u, c u ≠ 0) (hV : Vᴴ * V = 1) (hU : ∀ u, IsUni (U u)) (u : ι) :
    hsSq (Kd (Btwist B c V U) (gaTw ga c) u - 1) = hsSq (Kd B ga u - 1) := by
  rw [Kd_tw_sub B ga c V U hc hV hU]
  exact hilbert_schmidt_unitary_invariant _ _ _ _ _ _ _ (by simpa using (hU u).2) (hU u).2
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
