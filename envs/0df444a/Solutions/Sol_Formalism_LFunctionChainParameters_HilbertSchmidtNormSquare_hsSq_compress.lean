-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_compress
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:13.265906+00:00
-- url     : https://prove2.me/submissions/462d6bb4-27fd-4c25-a09e-fd3b0c2ad463

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_conjTranspose
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_left_le

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
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution {a b c e : ℕ} (V : Matrix (Fin a) (Fin c) ℂ) (hV : Vᴴ * V = 1)
    (W : Matrix (Fin b) (Fin e) ℂ) (hW : Wᴴ * W = 1) (M : Matrix (Fin a) (Fin b) ℂ) :
    hsSq (Vᴴ * M * W) ≤ hsSq M := by
  have h1 := hsSq_left_le W hW (Vᴴ * M)ᴴ
  have h2 := hsSq_left_le V hV M
  rw [← Matrix.conjTranspose_mul, hsSq_conjTranspose, hsSq_conjTranspose] at h1
  linarith
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
