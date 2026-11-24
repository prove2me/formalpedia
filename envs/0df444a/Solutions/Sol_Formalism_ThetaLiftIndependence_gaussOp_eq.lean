-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.gaussOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:30.675448+00:00
-- url     : https://prove2.me/submissions/039f2c3b-478e-46ea-90b9-304975c17f65

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp
import Theorems.Thm_Formalism_ThetaLiftIndependence_GaussOperatorLemmas_core

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
open GaussOperatorLemmas
namespace Formalism.ThetaLiftIndependence
theorem _root_.solution : GaussOp := by
  intro 𝔽 V _ _ _ _ _ ψ ρ hψ v hv
  have hρ : ∀ (a b : 𝔽ˣ) (w : V), ρ a (ρ b w) = ρ (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  constructor
  · simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, hρ]
    have step : ∀ d : 𝔽ˣ, ψ (-(d : 𝔽)) • ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ (c * d⁻¹) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d) • ρ e v := by
      intro d
      rw [Finset.smul_sum, ← Fintype.sum_equiv (Equiv.mulRight d) (fun e => ψ (-(d : 𝔽)) •
        ψ ((e * d : 𝔽ˣ) : 𝔽) • ρ (e * d * d⁻¹) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [smul_smul, mul_inv_cancel_right, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv
  · simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, hρ]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have step : ∀ c : 𝔽ˣ, ∑ d : 𝔽ˣ, (ψ (d : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * d) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * c) • ρ e v := by
      intro c
      rw [← Fintype.sum_equiv (Equiv.mulLeft c) (fun e => (ψ ((c * e : 𝔽ˣ) : 𝔽) *
        ψ (-(c : 𝔽))) • ρ (c⁻¹ * (c * e)) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [inv_mul_cancel_left, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv
end Formalism.ThetaLiftIndependence
