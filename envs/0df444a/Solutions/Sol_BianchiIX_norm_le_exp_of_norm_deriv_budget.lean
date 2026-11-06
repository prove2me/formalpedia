-- Prove2me | solution 1 for BianchiIX.norm_le_exp_of_norm_deriv_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:55:20.659323+00:00
-- url     : https://prove2.me/submissions/ecf3894e-e020-43b7-bf16-df585bca04a2

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- A nondecreasing forcing budget gives a dimension-free variable-rate estimate. -/
theorem solution {f f' : ℝ → E} {z z' B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hB : ∀ t ∈ Icc a b, HasDerivAt B (B' t) t)
    (hB0 : ∀ t ∈ Icc a b, 0 ≤ B t) (hB' : ∀ t ∈ Icc a b, 0 ≤ B' t)
    (hinit : ‖f a‖ ≤ B a) (hclock : ∀ t ∈ Icc a b, z a ≤ z t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ z' t * ‖f t‖ + B' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ B t * Real.exp (z t - z a) := by
  intro t ht
  have H : ∀ δ ∈ Ioi (0 : ℝ),
      ‖f t‖ ≤ (B t + δ) * Real.exp (z t - z a + δ * (t - a)) := by
    intro δ hδ
    change 0 < δ at hδ
    let R := fun s => (B s + δ) * Real.exp (z s - z a + δ * (s - a))
    let R' := fun s => B' s * Real.exp (z s - z a + δ * (s - a)) + (z' s + δ) * R s
    have hR (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt R (R' s) s := by
      convert! ((hB s hs).add_const δ).mul
        ((((hz s hs).sub_const (z a)).add (((hasDerivAt_id' s).sub_const a).const_mul δ)).exp) using 1
      dsimp only [R, R', Pi.add_apply, Pi.sub_apply]
      ring
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary' (HasDerivAt.continuousOn hf)
      (fun s hs => (hf s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (B' := R')
      (by dsimp [R]; simp only [sub_self, mul_zero, add_zero, Real.exp_zero, mul_one]; linarith only [hinit, hδ])
      (HasDerivAt.continuousOn hR) (fun s hs => (hR s (Ico_subset_Icc_self hs)).hasDerivWithinAt) ?_ ht
    intro s hs heq
    have hb := hbound s (Ico_subset_Icc_self hs)
    rw [heq] at hb
    have hpos : 0 < R s := mul_pos (by linarith only [hB0 s (Ico_subset_Icc_self hs), hδ]) (Real.exp_pos _)
    have he : 1 ≤ Real.exp (z s - z a + δ * (s - a)) := Real.one_le_exp_iff.mpr
      (add_nonneg (sub_nonneg.mpr (hclock s (Ico_subset_Icc_self hs)))
        (mul_nonneg hδ.le (sub_nonneg.mpr hs.1)))
    have hforce := mul_le_mul_of_nonneg_left he (hB' s (Ico_subset_Icc_self hs))
    dsimp only [R']
    nlinarith only [hb, mul_pos hδ hpos, hforce]
  have hcont : ContinuousWithinAt
      (fun δ : ℝ => (B t + δ) * Real.exp (z t - z a + δ * (t - a))) (Ioi 0) 0 := by fun_prop
  have H0 := continuousWithinAt_const.closure_le
    (by simp only [closure_Ioi, self_mem_Ici] : (0 : ℝ) ∈ closure (Ioi 0)) hcont H
  simpa only [add_zero, zero_mul] using H0
