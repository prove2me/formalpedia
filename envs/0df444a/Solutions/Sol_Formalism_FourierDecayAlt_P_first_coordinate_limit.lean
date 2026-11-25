-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.first_coordinate_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:27.290735+00:00
-- url     : https://prove2.me/submissions/07b35a0a-3ff9-4169-84b4-cf730b2e3e1d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.Rho1Limit := by
  intro m D σ ρ' X B hX
  obtain ⟨h1, h2⟩ := leading_cofactor m X B ρ' hX
  rw [rho1, h1, h2, zero_pow (Nat.succ_ne_zero m), zero_mul, zero_sub, sub_zero]
  rcases neg_one_pow_eq_or ℂ m with h | h
  · rw [pow_add, h]; norm_num
  · rw [pow_add, h]; norm_num [neg_div_neg_eq]
end Formalism.FourierDecayAlt.P
