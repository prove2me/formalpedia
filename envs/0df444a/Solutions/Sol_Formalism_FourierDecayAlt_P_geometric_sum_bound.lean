-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.geometric_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:05.139606+00:00
-- url     : https://prove2.me/submissions/63eb4206-1d0d-495d-9279-bfb1df9cea64

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EnergyEstimateFromParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.GeomSum := by
  intro c x R hc hx hx1
  have ha0 : 0 ≤ Real.exp 1 * √c := by positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √c) := by positivity
  have hx1' : x * (2 * (1 + 2 * Real.exp 1 * √c)) ≤ 1 := by
    rw [le_div_iff₀ hden] at hx1
    exact hx1
  have hxlt : x < 1 := by nlinarith [mul_nonneg ha0 hx]
  have hgeom : ∑ p ∈ Finset.Icc 1 R, x ^ p ≤ x / (1 - x) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := R + 1) hx hxlt
    rw [pow_one] at h
    have hI : Finset.Ico 1 (R + 1) = Finset.Icc 1 R := by
      ext p
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rwa [hI] at h
  have h2 : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg ha0 hx]
  rw [← Finset.mul_sum]
  calc Real.exp 1 * √c * ∑ p ∈ Finset.Icc 1 R, x ^ p ≤ Real.exp 1 * √c * (2 * x) :=
        mul_le_mul_of_nonneg_left (hgeom.trans h2) ha0
    _ ≤ 1 / 2 := by nlinarith [mul_nonneg ha0 hx]
end Formalism.FourierDecayAlt.P
