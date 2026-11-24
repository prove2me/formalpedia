-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.norm_pow_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:06.625806+00:00
-- url     : https://prove2.me/submissions/b36ec7d2-1c06-4ebb-ab38-2f8fab7b66bd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution {ζ : ℂ} (h : ‖ζ‖ = 1) (i : ℕ) : ‖ζ ^ i - 1‖ ≤ i * ‖ζ - 1‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : ζ ^ (i + 1) - 1 = ζ * (ζ ^ i - 1) + (ζ - 1) := by ring
    rw [e]
    calc ‖ζ * (ζ ^ i - 1) + (ζ - 1)‖ ≤ ‖ζ * (ζ ^ i - 1)‖ + ‖ζ - 1‖ := norm_add_le _ _
      _ = ‖ζ ^ i - 1‖ + ‖ζ - 1‖ := by rw [norm_mul, h, one_mul]
      _ ≤ _ := by push_cast; linarith
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
