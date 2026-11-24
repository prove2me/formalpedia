-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.GaussOperatorLemmas.sum_units_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:46.899566+00:00
-- url     : https://prove2.me/submissions/0bfe5ad8-b510-4d83-9872-c027c2efa689

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp
import Theorems.Thm_Formalism_ThetaLiftIndependence_GaussOperatorLemmas_sum_units_eq_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.GaussOperatorLemmas
variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
namespace Formalism.ThetaLiftIndependence.GaussOperatorLemmas
theorem _root_.solution (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (a : 𝔽) :
    ∑ d : 𝔽ˣ, ψ (a * d) = (if a = 0 then (Fintype.card 𝔽 : ℂ) else 0) - 1 := by
  rw [sum_units_eq_sub (fun x => ψ (a * x))]
  simp only [mul_zero, AddChar.map_zero_eq_one]
  congr 1
  have h := AddChar.sum_mulShift a (AddChar.IsPrimitive.of_ne_one hψ)
  rw [Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm])
end Formalism.ThetaLiftIndependence.GaussOperatorLemmas
