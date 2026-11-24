-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Qm_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:37.849243+00:00
-- url     : https://prove2.me/submissions/532bcdc3-b9ee-4169-ad97-bcc520859e26

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement

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
    (hc : ∀ u, c u ≠ 0) (hU : ∀ u, IsUni (U u)) :
    Qm (Btwist B c V U) (gaTw ga c) = V * Qm B ga * Vᴴ := by
  unfold Qm
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold Btwist gaTw
  have hm : (V * B u * U u) * (V * B u * U u)ᴴ = V * (B u * (B u)ᴴ) * Vᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul]
    have : V * B u * U u * ((U u)ᴴ * ((B u)ᴴ * Vᴴ)) = V * (B u * (U u * (U u)ᴴ) * (B u)ᴴ) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, (hU u).2, Matrix.mul_one]
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hm, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, smul_smul]
  congr 1
  have h1 : (‖c u‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr (hc u)).ne'
  have h2 : c u * star (c u) = (‖c u‖ : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj']
  push_cast
  rw [mul_assoc, h2]
  field_simp
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
