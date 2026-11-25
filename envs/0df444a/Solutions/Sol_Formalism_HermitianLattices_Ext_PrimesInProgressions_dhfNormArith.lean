-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhfNormArith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:34:38.069805+00:00
-- url     : https://prove2.me/submissions/6ab3c840-74fa-49af-98b4-b357f9ae4121

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqFA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (D3 D4 P3 P4 S3 S4 I3 I4 A B : ℂ) (k : ℕ) (e3 e4 Dom X : ℝ)
    (h3 : ‖D3 - P3 + S3‖ ≤ e3) (h4 : ‖D4 - P4 + S4‖ ≤ e4)
    (hD3 : D3 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * A) (hD4 : D4 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * B)
    (hdom : ‖A + B‖ ≤ Dom) (hP : ‖P3 + P4 - I3 - I4‖ ≤ X) :
    ‖(S3 - I3) + (S4 - I4)‖ ≤ Dom / (k.factorial : ℝ) + X + e3 + e4 := by
  have hnf : ‖(-1 : ℂ) ^ k / (k.factorial : ℂ)‖ = 1 / (k.factorial : ℝ) := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hD : ‖D3 + D4‖ ≤ Dom / (k.factorial : ℝ) := by
    rw [hD3, hD4, ← mul_add, norm_mul, hnf, div_mul_eq_mul_div, one_mul]
    gcongr
  have e : (S3 - I3) + (S4 - I4) =
      ((D3 - P3 + S3) + (D4 - P4 + S4) - (D3 + D4)) + (P3 + P4 - I3 - I4) := by ring
  rw [e]
  have n1 := norm_add_le ((D3 - P3 + S3) + (D4 - P4 + S4) - (D3 + D4)) (P3 + P4 - I3 - I4)
  have n2 := norm_sub_le ((D3 - P3 + S3) + (D4 - P4 + S4)) (D3 + D4)
  have n3 := norm_add_le (D3 - P3 + S3) (D4 - P4 + S4)
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
