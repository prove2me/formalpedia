-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.FiniteFieldPlancherel.orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:22.142473+00:00
-- url     : https://prove2.me/submissions/659a306e-3006-471d-8c01-4c90f2717b7d

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_FFPlancherel
import Theorems.Thm_Formalism_ThetaLiftIndependence_FiniteFieldPlancherel_charSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.FiniteFieldPlancherel
open Classical
namespace Formalism.ThetaLiftIndependence.FiniteFieldPlancherel
theorem _root_.solution {𝔽 U : Type} [Field 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) [Fintype 𝔽] (f g : Module.Dual 𝔽 U) :
    ∑ e : U, star (ψ (f e)) * ψ (g e) = if f = g then (Fintype.card U : ℂ) else 0 := by
  have h : ∀ e, star (ψ (f e)) * ψ (g e) = ψ ((g - f) e) := by
    intro e
    rw [LinearMap.sub_apply, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj,
      Complex.star_def, mul_comm]
  simp_rw [h]
  rw [charSum ψ hψ]
  by_cases hfg : f = g
  · simp [hfg]
  · rw [if_neg hfg, if_neg (fun h' => hfg (sub_eq_zero.mp h').symm)]
end Formalism.ThetaLiftIndependence.FiniteFieldPlancherel
