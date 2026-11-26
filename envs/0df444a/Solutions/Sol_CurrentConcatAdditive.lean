-- Prove2me | solution 1 for CurrentConcatAdditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:51.888903+00:00
-- url     : https://prove2.me/submissions/573bc162-9a56-4cd1-ace5-85a96c4e9677

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurrentConcatAdditive
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open Set MeasureTheory
theorem _root_.solution {E : Type*} [MetricSpace E] (γ₁ γ₂ : Curve E)
    (h : γ₁.toFun γ₁.len = γ₂.toFun 0) (ω : Form1 E) :
    curveCurrent (curveConcat γ₁ γ₂ h) ω = curveCurrent γ₁ ω + curveCurrent γ₂ ω := by
-- BODY
  -- Step 1: the integrand of `curveCurrent η ω` is interval-integrable on every `a..b`.
  have hint : ∀ (η : Curve E) (a b : ℝ),
      IntervalIntegrable (fun t => ω.f (η.toFun t) * deriv (ω.pi ∘ η.toFun) t) volume a b := by
    intro η a b
    have hlip : LipschitzWith ω.piLip (ω.pi ∘ η.toFun) := by
      have hc := ω.pi_lipschitz.comp (CurveLipschitz η)
      simpa using hc
    have hcont : Continuous (ω.f ∘ η.toFun) :=
      ω.f_lipschitz.continuous.comp (CurveLipschitz η).continuous
    have hac : AbsolutelyContinuousOnInterval (ω.pi ∘ η.toFun) a b :=
      (hlip.lipschitzOnWith).absolutelyContinuousOnInterval
    have hderiv_int : IntervalIntegrable (deriv (ω.pi ∘ η.toFun)) volume a b :=
      hac.intervalIntegrable_deriv
    have := hderiv_int.continuousOn_mul (hcont.continuousOn (s := Set.uIcc a b))
    simpa [Function.comp] using this
  -- The underlying data of the concatenation.
  have hval : ∀ t : ℝ, (curveConcat γ₁ γ₂ h).toFun t
      = if t ≤ γ₁.len then γ₁.toFun t else γ₂.toFun (t - γ₁.len) := fun _ => rfl
  have hlen : (curveConcat γ₁ γ₂ h).len = γ₁.len + γ₂.len := rfl
  -- Derivatives agree with those of `γ₁` strictly left of the joint.
  have hderivL : ∀ t : ℝ, t < γ₁.len →
      deriv (ω.pi ∘ (curveConcat γ₁ γ₂ h).toFun) t = deriv (ω.pi ∘ γ₁.toFun) t := by
    intro t ht
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Iio_mem_nhds ht] with u hu
    simp only [Function.comp_apply, hval u, if_pos (le_of_lt (mem_Iio.mp hu))]
  -- Derivatives agree with the shifted ones of `γ₂` strictly right of the joint.
  have hderivR : ∀ t : ℝ, γ₁.len < t →
      deriv (ω.pi ∘ (curveConcat γ₁ γ₂ h).toFun) t = deriv (ω.pi ∘ γ₂.toFun) (t - γ₁.len) := by
    intro t ht
    have h1 : deriv (ω.pi ∘ (curveConcat γ₁ γ₂ h).toFun) t
        = deriv (fun u => (ω.pi ∘ γ₂.toFun) (u - γ₁.len)) t := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Ioi_mem_nhds ht] with u hu
      simp only [Function.comp_apply, hval u, if_neg (not_le.mpr (mem_Ioi.mp hu))]
    rw [h1, deriv_comp_sub_const (ω.pi ∘ γ₂.toFun) γ₁.len t]
  -- Step 2: split the integral at the joint.
  have hsplit : curveCurrent (curveConcat γ₁ γ₂ h) ω
      = (∫ t in (0:ℝ)..γ₁.len,
            ω.f ((curveConcat γ₁ γ₂ h).toFun t) * deriv (ω.pi ∘ (curveConcat γ₁ γ₂ h).toFun) t)
        + ∫ t in γ₁.len..(γ₁.len + γ₂.len),
            ω.f ((curveConcat γ₁ γ₂ h).toFun t) * deriv (ω.pi ∘ (curveConcat γ₁ γ₂ h).toFun) t := by
    rw [curveCurrent, hlen]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hint _ 0 γ₁.len) (hint _ γ₁.len (γ₁.len + γ₂.len))).symm
  -- Step 3: the first piece is `curveCurrent γ₁ ω`.
  have hae : ∀ᵐ x : ℝ ∂volume, x ≠ γ₁.len := by
    rw [MeasureTheory.ae_iff]
    simp
  have hleft : (∫ t in (0:ℝ)..γ₁.len,
        ω.f ((curveConcat γ₁ γ₂ h).toFun t) * deriv (ω.pi ∘ (curveConcat γ₁ γ₂ h).toFun) t)
      = curveCurrent γ₁ ω := by
    rw [curveCurrent]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxmem
    rw [Set.uIoc_of_le γ₁.len_nonneg] at hxmem
    have hlt : x < γ₁.len := lt_of_le_of_ne hxmem.2 hx
    rw [hderivL x hlt]
    simp only [hval x, if_pos (le_of_lt hlt)]
  -- Step 4: the second piece is `curveCurrent γ₂ ω`.
  have hright : (∫ t in γ₁.len..(γ₁.len + γ₂.len),
        ω.f ((curveConcat γ₁ γ₂ h).toFun t) * deriv (ω.pi ∘ (curveConcat γ₁ γ₂ h).toFun) t)
      = curveCurrent γ₂ ω := by
    have hstep : (∫ t in γ₁.len..(γ₁.len + γ₂.len),
          ω.f ((curveConcat γ₁ γ₂ h).toFun t) * deriv (ω.pi ∘ (curveConcat γ₁ γ₂ h).toFun) t)
        = ∫ t in γ₁.len..(γ₁.len + γ₂.len),
            ω.f (γ₂.toFun (t - γ₁.len)) * deriv (ω.pi ∘ γ₂.toFun) (t - γ₁.len) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with x hxmem
      rw [Set.uIoc_of_le (by linarith [γ₂.len_nonneg] : γ₁.len ≤ γ₁.len + γ₂.len)] at hxmem
      have hlt : γ₁.len < x := hxmem.1
      rw [hderivR x hlt]
      simp only [hval x, if_neg (not_le.mpr hlt)]
    rw [hstep, curveCurrent]
    have hshift := intervalIntegral.integral_comp_sub_right
      (a := γ₁.len) (b := γ₁.len + γ₂.len)
      (fun u => ω.f (γ₂.toFun u) * deriv (ω.pi ∘ γ₂.toFun) u) γ₁.len
    simpa using hshift
  rw [hsplit, hleft, hright]
