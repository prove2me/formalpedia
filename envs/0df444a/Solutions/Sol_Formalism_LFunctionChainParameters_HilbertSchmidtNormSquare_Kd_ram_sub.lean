-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.Kd_ram_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:33.271911+00:00
-- url     : https://prove2.me/submissions/4120acd5-e331-4248-8d27-a7cd999fe12a

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_Kp_ram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (hV : Isom V) (u : ι) :
    Kd (Bram B V) ga u - 1 = (V u)ᴴ * (Kd B ga u - 1) * V u := by
  have hV' : ∀ u, (V u)ᴴ * V u = 1 := hV
  have h := Kp_ram B V ga u u
  unfold Kd
  rw [h, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV' u]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
