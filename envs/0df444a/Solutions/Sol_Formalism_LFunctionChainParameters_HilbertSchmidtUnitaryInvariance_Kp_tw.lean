-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Kp_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:42:44.5698+00:00
-- url     : https://prove2.me/submissions/9322ab53-3cd2-4e78-823e-2e3953d85fc1

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_sqrt_gaTw

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
    (hc : ∀ u, c u ≠ 0) (hV : Vᴴ * V = 1) (u u' : ι) :
    Kp (Btwist B c V U) (gaTw ga c) u u' = phase c u u' • ((U u)ᴴ * Kp B ga u u' * U u') := by
  unfold Kp
  rw [sqrt_gaTw ga c hc]
  unfold Btwist phase
  have hm : (V * B u * U u)ᴴ * (V * B u' * U u') = (U u)ᴴ * ((B u)ᴴ * B u') * U u' := by
    rw [conjTranspose_mul, conjTranspose_mul]
    have : (U u)ᴴ * ((B u)ᴴ * Vᴴ) * (V * B u' * U u')
        = (U u)ᴴ * ((B u)ᴴ * (Vᴴ * V) * B u') * U u' := by simp only [Matrix.mul_assoc]
    rw [this, hV, Matrix.mul_one]
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hm, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  simp only [Complex.star_def]
  ring
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
