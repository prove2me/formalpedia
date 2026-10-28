-- Prove2me | solution 1 for AvramDividend.Classical.causal_gaussian_weighted_series_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:51:57.321851+00:00
-- url     : https://prove2.me/submissions/054b5b9e-e7d0-4bbc-bd4e-bdea407b4cc2

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_exponential_tsum_untwist
open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Undo exponential damping in the Gaussian correction series. -/
theorem solution
    (P H : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a w : ℝ)
    (hH : ∀ n : ℕ, H n = fun x : ℝ =>
      (Real.exp (-w * x) *
        (∫ t in Ioc (0 : ℝ) x,
          Real.exp (w * t) * P n t ∂volume)) / a)
    (hg : g = fun y : ℝ => 1 / a + Real.exp (w * y) *
      (∑' n : ℕ, (Real.exp (-w * y) *
        (∫ t in Ioc (0 : ℝ) y,
          Real.exp (w * t) * P n t ∂volume)) / a)) :
    ∃ Q : ℕ → ℝ → ℝ,
      Q 0 = (fun _ : ℝ => 1 / a) ∧
      (∀ n : ℕ, Q (n + 1) =
        fun x : ℝ => Real.exp (w * x) * H n x) ∧
      (∀ n : ℕ, Q (n + 1) =
        fun x : ℝ => (1 / a) *
          (∫ t in Ioc (0 : ℝ) x,
            Real.exp (w * t) * P n t ∂volume)) ∧
      (∀ x : ℝ, Summable (fun n : ℕ => Q n x) →
        g x = ∑' n : ℕ, Q n x) := by
  let Q : ℕ → ℝ → ℝ := fun n =>
    match n with
    | 0 => fun _ => 1 / a
    | m + 1 => fun x => Real.exp (w * x) * H m x
  have hQ0 : Q 0 = fun _ : ℝ => 1 / a := rfl
  have hQstep : ∀ n : ℕ, Q (n + 1) =
      fun x : ℝ => Real.exp (w * x) * H n x := by
    intro n
    rfl
  have hQsucc : ∀ n : ℕ, Q (n + 1) =
      fun x : ℝ => (1 / a) *
        (∫ t in Ioc (0 : ℝ) x,
          Real.exp (w * t) * P n t ∂volume) := by
    intro n
    funext x
    change Real.exp (w * x) * H n x = _
    rw [congrFun (hH n) x]
    have hc : Real.exp (w * x) * Real.exp (-w * x) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      Real.exp (w * x) *
          ((Real.exp (-w * x) *
            (∫ t in Ioc (0 : ℝ) x,
              Real.exp (w * t) * P n t ∂volume)) / a)
          = (Real.exp (w * x) * Real.exp (-w * x)) *
            ((∫ t in Ioc (0 : ℝ) x,
              Real.exp (w * t) * P n t ∂volume) / a) := by ring
      _ = (∫ t in Ioc (0 : ℝ) x,
            Real.exp (w * t) * P n t ∂volume) / a := by rw [hc]; ring
      _ = (1 / a) *
            (∫ t in Ioc (0 : ℝ) x,
              Real.exp (w * t) * P n t ∂volume) := by ring
  have hgsum : ∀ x : ℝ, g x =
      1 / a + ∑' n : ℕ,
        (∫ t in Ioc (0 : ℝ) x,
          Real.exp (w * t) * P n t ∂volume) / a := by
    intro x
    rw [congrFun hg x]
    rw [causal_exponential_tsum_untwist
      (fun n : ℕ => ∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P n t ∂volume) w x a]
  refine ⟨Q, hQ0, hQstep, hQsucc, ?_⟩
  intro x hsum
  calc
    g x = 1 / a + ∑' n : ℕ,
        (∫ t in Ioc (0 : ℝ) x,
          Real.exp (w * t) * P n t ∂volume) / a := hgsum x
    _ = Q 0 x + ∑' n : ℕ, Q (n + 1) x := by
      rw [congrFun hQ0 x]
      congr 1
      refine tsum_congr (fun n => ?_)
      calc
        (∫ t in Ioc (0 : ℝ) x,
          Real.exp (w * t) * P n t ∂volume) / a =
          (1 / a) * (∫ t in Ioc (0 : ℝ) x,
            Real.exp (w * t) * P n t ∂volume) := by ring
        _ = Q (n + 1) x := (congrFun (hQsucc n) x).symm
    _ = ∑' n : ℕ, Q n x := (hsum).tsum_eq_zero_add.symm
