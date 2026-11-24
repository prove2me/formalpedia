-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cof_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:53.253157+00:00
-- url     : https://prove2.me/submissions/dad2064c-abc8-4506-82e8-2dce66cee3ac

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_sum_mul_zero_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_leading_cofactor


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
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hS : IsStrictUpper X)
    (B : Fin (m + 1) → ℂ) (t : ℂ) :
    Cof X B t = (∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)) + (-1) ^ m * ∏ k, xOf X B k := by
  have h := (Formalism.FourierDecayAlt.P.leading_cofactor m X B 0 hS).1
  rw [Cof, sum_mul_zero_pow m (fun j => ((-X) ^ j *ᵥ B) 0)] at h
  rw [Cof, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, h]
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
