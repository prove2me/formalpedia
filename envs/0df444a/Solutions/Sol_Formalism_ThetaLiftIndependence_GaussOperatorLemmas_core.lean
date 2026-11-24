-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.GaussOperatorLemmas.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:37.121432+00:00
-- url     : https://prove2.me/submissions/98e6cfcc-e067-4fd9-a22a-35b7be9e346d

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp
import Theorems.Thm_Formalism_ThetaLiftIndependence_GaussOperatorLemmas_sum_units_char

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
theorem _root_.solution (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) (v : V) (hv : ∑ c : 𝔽ˣ, ρ c v = 0) :
    ∑ e : 𝔽ˣ, (∑ d : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d)) • ρ e v = (Fintype.card 𝔽 : ℂ) • v := by
  simp_rw [sum_units_char ψ hψ, sub_smul, one_smul, Finset.sum_sub_distrib, hv, sub_zero,
    sub_eq_zero, Units.val_eq_one, ite_smul, zero_smul]
  simp
end Formalism.ThetaLiftIndependence.GaussOperatorLemmas
