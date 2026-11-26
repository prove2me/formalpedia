-- Prove2me | solution 1 for CurrentFormAddPi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:14.152853+00:00
-- url     : https://prove2.me/submissions/3e71a159-fb8b-4072-b325-b793fb1b61b9

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurrentFormAddPi
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (ω1 ω2 ω12 : Form1 E)
    (hf1 : ω1.f = ω12.f) (hf2 : ω2.f = ω12.f)
    (hpi : ∀ x, ω12.pi x = ω1.pi x + ω2.pi x) :
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
  have h1 : LipschitzWith ω1.piLip (ω1.pi ∘ γ.toFun) := by
    have h := ω1.pi_lipschitz.comp (CurveLipschitz γ); simpa using h
  have h2 : LipschitzWith ω2.piLip (ω2.pi ∘ γ.toFun) := by
    have h := ω2.pi_lipschitz.comp (CurveLipschitz γ); simpa using h
  have ha1 : AbsolutelyContinuousOnInterval (ω1.pi ∘ γ.toFun) 0 γ.len :=
    (h1.lipschitzOnWith).absolutelyContinuousOnInterval
  have ha2 : AbsolutelyContinuousOnInterval (ω2.pi ∘ γ.toFun) 0 γ.len :=
    (h2.lipschitzOnWith).absolutelyContinuousOnInterval
  have heq : (ω12.pi ∘ γ.toFun) = (fun s => (ω1.pi ∘ γ.toFun) s + (ω2.pi ∘ γ.toFun) s) := by
    funext s; exact hpi _
  unfold curveCurrent
  rw [← intervalIntegral.integral_add (cint ω1 _ _) (cint ω2 _ _)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ha1.ae_differentiableAt, ha2.ae_differentiableAt] with t ht1 ht2 htmem
  have hmem : t ∈ Set.uIcc (0 : ℝ) γ.len := by
    simpa [Set.uIoc, Set.uIcc] using Set.uIoc_subset_uIcc htmem
  have hadd : deriv (fun s => (ω1.pi ∘ γ.toFun) s + (ω2.pi ∘ γ.toFun) s) t
      = deriv (ω1.pi ∘ γ.toFun) t + deriv (ω2.pi ∘ γ.toFun) t :=
    deriv_add (ht1 hmem) (ht2 hmem)
  rw [heq, hadd, hf1, hf2]; ring
