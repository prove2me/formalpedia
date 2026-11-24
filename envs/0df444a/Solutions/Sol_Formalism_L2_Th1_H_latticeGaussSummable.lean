-- Prove2me | solution 1 for Formalism.L2.Th1.H.latticeGaussSummable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:40:02.404715+00:00
-- url     : https://prove2.me/submissions/341f08dc-7a63-4d0b-a862-0f7846dd8ec5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Theorems.Thm_Formalism_L2_Th1_H_half_sq_sub_le
import Theorems.Thm_Formalism_L2_Th1_H_summable_gauss_of_discrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : LatGaussSummable := by
  intro V _ _ _ Λ hΛ c r hc
  have : DiscreteTopology Λ := hΛ.1
  have hs : Summable fun x : Λ => Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2) :=
    summable_gauss_of_discrete Λ (by positivity)
  refine ⟨fun x => Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2), hs.mul_left _, ?_⟩
  intro x z₀ hz
  show _ ≤ Real.exp (c * r ^ 2) * Real.exp (-(c / 2) * ‖(x : V)‖ ^ 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := half_sq_sub_le (x : V) z₀
  have h2 : ‖z₀‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg z₀) hz 2
  nlinarith
end Formalism.L2.Th1.H
