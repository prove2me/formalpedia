-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.minimum_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:41.425022+00:00
-- url     : https://prove2.me/submissions/51953488-78c0-4160-a5a5-4f43d510c249

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.MinShape := by
  intro f K l x X M hl hx h
  have hprod : (∏ v, min 1 ((x v / l v) ^ K)) =
      ∏ v ∈ univ.filter (fun v => x v < l v), (x v / l v) ^ K := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    split_ifs with hv
    · apply min_eq_right
      exact pow_le_one₀ (div_nonneg (hx v) (hl v).le) ((div_lt_one (hl v)).mpr hv).le
    · apply min_eq_left
      apply one_le_pow₀
      rw [one_le_div (hl v)]
      exact not_lt.mp hv
  have hPl : 0 < ∏ v ∈ univ.filter (fun v => x v < l v), l v ^ K :=
    Finset.prod_pos (fun v _ => pow_pos (hl v) K)
  rw [hprod]
  simp only [div_pow]
  rw [Finset.prod_div_distrib, div_mul_eq_mul_div, le_div_iff₀ hPl, mul_comm X]
  exact h _
end Formalism.FourierDecayAlt.P
