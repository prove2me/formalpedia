-- Prove2me | solution 1 for ConservationLaws.work_energy_theorem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:55:09.985461+00:00
-- url     : https://prove2.me/submissions/96062ca9-5797-45eb-88a4-63a63ec82b89

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {d : ℕ} (m : ℝ) (hm : 0 < m)
    (F : ℝ → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (x v a : ℝ → EuclideanSpace ℝ (Fin d))
    (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hnewton : ∀ t, m • a t = F t) :
    ∀ t₀ t₁, (1 / 2 : ℝ) * m * ‖v t₁‖ ^ 2 -
      (1 / 2 : ℝ) * m * ‖v t₀‖ ^ 2 =
      ∫ t in t₀..t₁, inner ℝ (F t) (v t) := by
  let K : ℝ → ℝ := fun t => (1 / 2 : ℝ) * m * ‖v t‖ ^ 2
  have hK (t : ℝ) :
      HasDerivAt K (inner ℝ (F t) (v t)) t := by
    have hsq := (hv t).norm_sq
    have hkm := hsq.const_mul ((1 / 2 : ℝ) * m)
    have heq : ((1 / 2 : ℝ) * m) *
        (2 * inner ℝ (v t) (a t)) = inner ℝ (F t) (v t) := by
      calc
        _ = m * inner ℝ (v t) (a t) := by ring
        _ = inner ℝ (m • a t) (v t) := by
          simp [real_inner_comm, inner_smul_left]
        _ = inner ℝ (F t) (v t) := by rw [hnewton t]
    change HasDerivAt K (((1 / 2 : ℝ) * m) *
        (2 * inner ℝ (v t) (a t))) t at hkm
    rw [heq] at hkm
    exact hkm
  have hvcont : Continuous v :=
    continuous_iff_continuousAt.mpr (fun t => (hv t).continuousAt)
  have hcont : Continuous (fun t => inner ℝ (F t) (v t)) :=
    hF.inner hvcont
  intro t₀ t₁
  have hint : IntervalIntegrable (fun t => inner ℝ (F t) (v t))
      volume t₀ t₁ := hcont.intervalIntegrable t₀ t₁
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hK t) hint
  exact hftc.symm
