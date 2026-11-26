-- Prove2me | solution 1 for CurrentResolutionAdditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:05.307799+00:00
-- url     : https://prove2.me/submissions/09779465-9a68-472d-89c5-981d1bc82021

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (ω : Form1 E)
    (k : ℕ) (s : ℕ → ℝ) (hmono : MonotoneOn s (Set.Icc 0 k)) (h0 : s 0 = 0) (hk : s k = γ.len) :
    curveCurrent γ ω =
      ∑ i ∈ Finset.range k, ∫ t in (s i)..(s (i + 1)), ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t := by
-- BODY
  have hlip : LipschitzWith ω.piLip (ω.pi ∘ γ.toFun) := by
    have h := ω.pi_lipschitz.comp (CurveLipschitz γ)
    simpa using h
  have hcont : Continuous (ω.f ∘ γ.toFun) :=
    ω.f_lipschitz.continuous.comp (CurveLipschitz γ).continuous
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (fun t => ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t) volume a b := by
    intro a b
    have hac : AbsolutelyContinuousOnInterval (ω.pi ∘ γ.toFun) a b :=
      (hlip.lipschitzOnWith).absolutelyContinuousOnInterval
    have hderiv_int : IntervalIntegrable (deriv (ω.pi ∘ γ.toFun)) volume a b :=
      hac.intervalIntegrable_deriv
    have := hderiv_int.continuousOn_mul (hcont.continuousOn (s := Set.uIcc a b))
    simpa [Function.comp] using this
  have main : ∀ n : ℕ, ∀ t : ℕ → ℝ, MonotoneOn t (Set.Icc 0 n) →
      (∫ u in (t 0)..(t n), ω.f (γ.toFun u) * deriv (ω.pi ∘ γ.toFun) u) =
        ∑ i ∈ Finset.range n, ∫ u in (t i)..(t (i + 1)), ω.f (γ.toFun u) * deriv (ω.pi ∘ γ.toFun) u := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ m ih =>
      intro t hmonot
      have hmono_m : MonotoneOn t (Set.Icc 0 m) :=
        hmonot.mono (fun x hx => ⟨hx.1, hx.2.trans m.le_succ⟩)
      rw [Finset.sum_range_succ, ← ih t hmono_m,
        intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have h := main k s hmono
  rw [h0, hk] at h
  unfold curveCurrent
  rw [h]
