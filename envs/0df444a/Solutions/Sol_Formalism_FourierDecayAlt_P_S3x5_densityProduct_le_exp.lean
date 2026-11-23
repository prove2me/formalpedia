-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.densityProduct_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:14.579807+00:00
-- url     : https://prove2.me/submissions/2f8a5434-ea56-4d99-b4ee-4698c5caf99b

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Finset Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (lo hi : ℤ) (hlo : 1 ≤ lo) :
    densP η q lo hi ≤ Real.exp (∑ i ∈ Finset.Icc lo hi, (q : ℝ) ^ (-i)) := by
  unfold densP
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi'
    exact (factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)).le
  · intro i hi'
    have h1 := (factor_bounds η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)).2
    have h2 := Real.add_one_le_exp ((q : ℝ) ^ (-i))
    linarith
end Formalism.FourierDecayAlt.P.S3x5
