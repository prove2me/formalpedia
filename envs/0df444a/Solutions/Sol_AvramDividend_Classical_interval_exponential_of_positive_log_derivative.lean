-- Prove2me | solution 1 for AvramDividend.Classical.interval_exponential_of_positive_log_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:16:06.101792+00:00
-- url     : https://prove2.me/submissions/c455d518-6985-4a06-9a2d-34b4bfb85fea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology ENNReal

theorem solution
    (V g : ℝ → ℝ)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hgcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      V b = V a * Real.exp (∫ t in a..b, g t) := by
  have hlog (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y : ℝ => Real.log (V y)) (g x) x := by
    have hv : V x ≠ 0 := ne_of_gt (hVpos x hx)
    have hd := (hVderiv x hx).log hv
    have he : V x * g x / V x = g x := by
      field_simp [hv]
    simpa only [he] using hd
  intro a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hint : IntervalIntegrable g volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hgcont.mono hsub)
  have hftc :
      (∫ t in a..b, g t) =
        Real.log (V b) - Real.log (V a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => Real.log (V y))
    · intro x hx
      have hxab : x ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using hx
      exact hlog x (lt_of_lt_of_le ha hxab.1)
    · exact hint
  have hbLog :
      Real.log (V b) =
        Real.log (V a) + ∫ t in a..b, g t := by
    rw [hftc]
    ring
  calc
    V b = Real.exp (Real.log (V b)) :=
      (Real.exp_log (hVpos b hb)).symm
    _ = Real.exp (Real.log (V a) + ∫ t in a..b, g t) := by
      rw [hbLog]
    _ = Real.exp (Real.log (V a)) * Real.exp (∫ t in a..b, g t) := by
      rw [Real.exp_add]
    _ = V a * Real.exp (∫ t in a..b, g t) := by
      rw [Real.exp_log (hVpos a ha)]
