-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.twist_ramified_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:28.695804+00:00
-- url     : https://prove2.me/submissions/16aa5a92-a7bb-4c4a-9f2e-8700d2d4e446

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_twist_invariance
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_gaTw_one
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_isUni_one
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Brow_eq

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
theorem _root_.solution : TwRamFactor := by
  intro ι _ Dall D' d r Pf Vr ga c V U W hc hV hU hW hVr
  refine ⟨fun u => ?_, fun u => ?_, fun Dstar η0 η1 e0 => ?_⟩
  · unfold Brow Btwist Bram VrS
    simp only [Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  · unfold VrS
    rw [conjTranspose_mul]
    have : (U u)ᴴ * (Vr u)ᴴ * (Vr u * U u) = (U u)ᴴ * ((Vr u)ᴴ * Vr u) * U u := by
      simp only [Matrix.mul_assoc]
    rw [this, hVr u, Matrix.mul_one, (hU u).1]
  · obtain ⟨-, -, -, i3⟩ := twist_invariance ι Dall Dall d Pf ga c V (fun _ => 1) hc hV
      (fun _ => isUni_one _)
    obtain ⟨-, -, -, j3⟩ := twist_invariance ι Dall D' d (Btwist Pf c V (fun _ => 1)) (gaTw ga c)
      (fun _ => 1) W (fun _ => 1) (fun _ => one_ne_zero) hW (fun _ => isUni_one _)
    rw [gaTw_one, ← Brow_eq] at j3
    exact (j3 _ _ _ _).trans (i3 _ _ _ _)
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
