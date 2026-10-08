-- Prove2me | solution 1 for DenardoDP.Contraction.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:57:10.321259+00:00
-- url     : https://prove2.me/submissions/a18311f0-49d1-4426-af9e-c201d0af5690

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

open DenardoDP.Contraction in
theorem DenardoDP_Contraction_theorem1_modulus {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω)
    (c : ℝ) (hH : IsPolicyOperator h H) (hc : ContractionAssumption h c)
    (δ : (x : Ω) → D x) (u w : BFun Ω) :
    dist (H δ u) (H δ w) ≤ c * dist u w := by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le (mul_nonneg hc.1 dist_nonneg) fun x => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, hH, hH]
  exact hc.2.2 u w x (δ x)

open DenardoDP.Contraction in
theorem solution {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω)
    (c : ℝ) (v : ((x : Ω) → D x) → BFun Ω)
    (hH : IsPolicyOperator h H) (hc : ContractionAssumption h c)
    (hv : ∀ δ, H δ (v δ) = v δ) :
    ∀ (δ : (x : Ω) → D x) (w : BFun Ω),
      dist (v δ) w ≤ dist (H δ w) w / (1 - c) := by
  intro δ w
  have h1 : dist (v δ) w ≤ dist (v δ) (H δ w) + dist (H δ w) w := dist_triangle _ _ _
  have h2 : dist (v δ) (H δ w) ≤ c * dist (v δ) w := by
    have := DenardoDP_Contraction_theorem1_modulus h H c hH hc δ (v δ) w
    rwa [hv] at this
  have hc1 : 0 < 1 - c := by linarith [hc.2.1]
  rw [le_div_iff₀ hc1]
  nlinarith
