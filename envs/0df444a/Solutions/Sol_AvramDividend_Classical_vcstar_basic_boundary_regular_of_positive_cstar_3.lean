-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_basic_boundary_regular_of_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:59:35.193469+00:00
-- url     : https://prove2.me/submissions/e3459075-727d-43a6-821c-2595a1addd7e

import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Canonical positive-barrier boundary regularity from nonnegative
scale-function slope, by direct continuous pasting of both branches. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      ∀ y < 0, vcstar W y = 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 < a := ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hWcont : ContinuousOn W (Ici (0 : ℝ)) := hW.2.2.1
  have hWnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x := hW.2.1
  have hder : 0 ≤ deriv W a :=
    scaleFunction_deriv_nonneg X q W hW a ha
  have hscale : scaleDeriv W a = ((deriv W a : ℝ) : EReal) := by
    simp [scaleDeriv, ha0]
  have hdiv (x : ℝ) : divE (W x) (scaleDeriv W a) = W x / deriv W a := by
    simp [hscale, divE]
  let f : ℝ → ℝ := (Iic a).piecewise
    (fun x => W x / deriv W a)
    (fun x => x - a + W a / deriv W a)
  have hbelow : ContinuousOn (fun x => W x / deriv W a) (Ici 0) :=
    hWcont.div_const _
  have habove : ContinuousOn (fun x : ℝ => x - a + W a / deriv W a) (Ici 0) :=
    (continuous_id.sub continuous_const |>.add continuous_const).continuousOn
  have hbound : EqOn (fun x => W x / deriv W a)
      (fun x => x - a + W a / deriv W a)
      (Ici (0 : ℝ) ∩ frontier (Iic a)) := by
    intro x hx
    have hxa : x = a := by simpa [frontier_Iic] using hx.2
    subst x
    ring
  have hpiece : ContinuousOn f (Ici 0) := by
    have h := continuousOn_piecewise_ite hbelow habove (by rfl) hbound
    simpa [f] using h
  have heq : EqOn (barrierValue W a) f (Ici 0) := by
    intro x hx
    have hx0 : ¬ x < 0 := not_lt.mpr hx
    by_cases hxa : x ≤ a
    · simp [barrierValue, f, Set.piecewise, hx0, hxa, hdiv]
    · simp [barrierValue, f, Set.piecewise, hx0, hxa, hdiv]
  have hcont : ContinuousOn (barrierValue W a) (Ici 0) :=
    hpiece.congr heq
  have hbound0 : 0 ≤ barrierValue W a 0 := by
    have h0 : (0 : ℝ) ≤ a := le_of_lt ha
    have hb : barrierValue W a 0 = W 0 / deriv W a := by
      simp [barrierValue, h0, hdiv]
    rw [hb]
    exact div_nonneg (hWnonneg 0 le_rfl) hder
  have hneg : ∀ y < 0, barrierValue W a y = 0 := by
    intro y hy
    simp [barrierValue, hy]
  simpa [vcstar, a] using
    (show ContinuousOn (barrierValue W a) (Ici 0) ∧
        0 ≤ barrierValue W a 0 ∧
        ∀ y < 0, barrierValue W a y = 0 from
      ⟨hcont, hbound0, hneg⟩)
