-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_positive_barrier_boundary_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:48:51.012989+00:00
-- url     : https://prove2.me/submissions/2374b009-9609-41a7-894b-f1c1aa19a590

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Topology

/-- Positive derivative normalisation glues the scale-ratio branch
continuously to the upper affine branch, including the zero boundary. -/
theorem solution
    (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hWcont : ContinuousOn W (Ici 0))
    (hWnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hder : 0 < deriv W a) :
    ContinuousOn (barrierValue W a) (Ici 0) ∧
      0 ≤ barrierValue W a 0 ∧
      ∀ y < 0, barrierValue W a y = 0 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
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
  refine ⟨hpiece.congr heq, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ a := le_of_lt ha
    have hb : barrierValue W a 0 = W 0 / deriv W a := by
      simp [barrierValue, h0, hdiv]
    rw [hb]
    exact div_nonneg (hWnonneg 0 le_rfl) (le_of_lt hder)
  · intro y hy
    simp [barrierValue, hy]
