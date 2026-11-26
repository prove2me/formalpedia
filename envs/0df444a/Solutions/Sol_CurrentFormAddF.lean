-- Prove2me | solution 1 for CurrentFormAddF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:04.302868+00:00
-- url     : https://prove2.me/submissions/32cd6c6b-9411-497b-ad90-e92c2d7a58a6

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurrentFormAddF
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (ω1 ω2 ω12 : Form1 E)
    (hpi1 : ω1.pi = ω12.pi) (hpi2 : ω2.pi = ω12.pi)
    (hf : ∀ x, ω12.f x = ω1.f x + ω2.f x) :
    curveCurrent γ ω12 = curveCurrent γ ω1 + curveCurrent γ ω2 := by
-- BODY
  have cint : ∀ (ω : Form1 E) (a b : ℝ),
      IntervalIntegrable (fun t => ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t) volume a b := by
    intro ω a b
    have hlip : LipschitzWith ω.piLip (ω.pi ∘ γ.toFun) := by
      have h := ω.pi_lipschitz.comp (CurveLipschitz γ); simpa using h
    have hcont : Continuous (ω.f ∘ γ.toFun) :=
      ω.f_lipschitz.continuous.comp (CurveLipschitz γ).continuous
    have hac : AbsolutelyContinuousOnInterval (ω.pi ∘ γ.toFun) a b :=
      (hlip.lipschitzOnWith).absolutelyContinuousOnInterval
    have := hac.intervalIntegrable_deriv.continuousOn_mul (hcont.continuousOn (s := Set.uIcc a b))
    simpa [Function.comp] using this
  unfold curveCurrent
  rw [← intervalIntegral.integral_add (cint ω1 _ _) (cint ω2 _ _)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [hf, hpi1, hpi2]; ring
