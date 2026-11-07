-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn17_inhomogeneous_first_order_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:42:16.138255+00:00
-- url     : https://prove2.me/submissions/ce5cbc30-bb80-4717-ba31-fa8be85ba419

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_first_order_exp_comparison_v2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
noncomputable section

theorem solution
    (rpos rneg a : ℝ) (hgap : rneg < rpos) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici a))
    (hwDiff : DifferentiableOn ℝ w (Ioi a))
    (B : ℝ) (hB : 0 ≤ B)
    (hDer : ∀ x : ℝ, a < x →
      deriv w x ≤ rpos * w x + B * Real.exp (rneg * (x - a))) :
    ∀ x : ℝ, a ≤ x →
      w x ≤ (w a + B / (rpos - rneg)) * Real.exp (rpos * (x - a)) := by
  let C : ℝ := B / (rpos - rneg)
  have hGap : 0 < rpos - rneg := sub_pos.mpr hgap
  have hC : 0 ≤ C := div_nonneg hB (le_of_lt hGap)
  have hBC : C * (rpos - rneg) = B := by
    dsimp [C]
    exact div_mul_cancel₀ B (ne_of_gt hGap)
  let v : ℝ → ℝ := fun t => w t + C * Real.exp (rneg * (t - a))
  have hvCont : ContinuousOn v (Ici a) := by
    have he : Continuous (fun t : ℝ => C * Real.exp (rneg * (t - a))) := by
      fun_prop
    exact hwCont.add he.continuousOn
  have hvHasDeriv : ∀ t : ℝ, a < t →
      HasDerivAt v (deriv w t + C * (rneg * Real.exp (rneg * (t - a)))) t := by
    intro t ht
    have hw : HasDerivAt w (deriv w t) t :=
      (hwDiff.differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
    have hlin : HasDerivAt (fun s : ℝ => rneg * (s - a)) rneg t := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).sub_const a).const_mul rneg
    have he : HasDerivAt (fun s : ℝ => Real.exp (rneg * (s - a)))
        (rneg * Real.exp (rneg * (t - a))) t := by
      simpa only [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (rneg * (t - a))).comp t hlin
    exact hw.add (he.const_mul C)
  have hvDiff : DifferentiableOn ℝ v (Ioi a) := by
    intro t ht
    exact (hvHasDeriv t ht).differentiableAt.differentiableWithinAt
  have hvLe : ∀ t : ℝ, a < t → deriv v t ≤ rpos * v t := by
    intro t ht
    have heq := (hvHasDeriv t ht).deriv
    calc
      deriv v t = deriv w t + C * (rneg * Real.exp (rneg * (t - a))) := heq
      _ ≤ rpos * w t + B * Real.exp (rneg * (t - a)) +
          C * (rneg * Real.exp (rneg * (t - a))) := by
            linarith [hDer t ht]
      _ = rpos * v t := by
        dsimp [v]
        rw [← hBC]
        ring
  have hComparison :=
    AvramDividend.Classical.avram_p4_f4_turn16_first_order_exp_comparison_v2
      v rpos a hvCont hvDiff hvLe
  intro x hx
  have hV : w x ≤ v x := by
    dsimp [v]
    have he : 0 ≤ C * Real.exp (rneg * (x - a)) :=
      mul_nonneg hC (le_of_lt (Real.exp_pos _))
    linarith
  calc
    w x ≤ v x := hV
    _ ≤ v a * Real.exp (rpos * (x - a)) := hComparison x hx
    _ = (w a + B / (rpos - rneg)) * Real.exp (rpos * (x - a)) := by
      simp [v, C]
