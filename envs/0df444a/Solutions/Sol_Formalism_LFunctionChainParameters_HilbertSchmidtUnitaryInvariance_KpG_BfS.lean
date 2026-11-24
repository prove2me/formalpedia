-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.KpG_BfS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:44:14.228655+00:00
-- url     : https://prove2.me/submissions/7a1fa436-c40f-4366-bd55-72d41f8ccf96

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_WfrS_isom

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
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution {ι : Type} [Fintype ι] {Dall D D1 : ℕ} {d : ι → ℕ}
    (Pf : ∀ u, Matrix (Fin Dall) (Fin (d u)) ℂ) (c : ι → ℂ) (V : Matrix (Fin Dall) (Fin Dall) ℂ)
    (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ) (h : OrthFrame J J1)
    (g : ι → ℝ) (u u' : ι) :
    MatrixLatticeEstimates.KpG (BfS Pf c V J J1) g u u' = Kp (Btwist Pf c V (fun _ => 1)) g u u' := by
  unfold MatrixLatticeEstimates.KpG Kp BfS Btwist
  have key : (WfrS J J1 * (V * Pf u))ᴴ * (WfrS J J1 * (V * Pf u')) = (V * Pf u)ᴴ * (V * Pf u') := by
    rw [conjTranspose_mul]
    have : (V * Pf u)ᴴ * (WfrS J J1)ᴴ * (WfrS J J1 * (V * Pf u'))
        = (V * Pf u)ᴴ * ((WfrS J J1)ᴴ * WfrS J J1) * (V * Pf u') := by
      simp only [Matrix.mul_assoc]
    rw [this, WfrS_isom J J1 h, Matrix.mul_one]
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, key]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
