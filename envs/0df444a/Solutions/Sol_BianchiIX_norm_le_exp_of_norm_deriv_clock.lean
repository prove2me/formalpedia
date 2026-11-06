-- Prove2me | solution 1 for BianchiIX.norm_le_exp_of_norm_deriv_clock
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:03:08.563318+00:00
-- url     : https://prove2.me/submissions/6331e8b3-34bf-4313-ade1-de92d7a77eea

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- A primitive of the variable growth rate gives a dimension-free norm bound. -/
theorem solution {f f' : ℝ → E} {z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ z' t * ‖f t‖) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ * Real.exp (z t - z a) := by
  intro t ht
  have H : ∀ ε ∈ Ioi (0 : ℝ),
      ‖f t‖ ≤ (‖f a‖ + ε) * Real.exp (z t - z a + ε * (t - a)) := by
    intro ε hε
    change 0 < ε at hε
    let B := fun s => (‖f a‖ + ε) * Real.exp (z s - z a + ε * (s - a))
    have hB (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt B ((z' s + ε) * B s) s := by
      convert! (((hz s hs).sub_const (z a)).add
        (((hasDerivAt_id' s).sub_const a).const_mul ε)).exp.const_mul (‖f a‖ + ε) using 1
      dsimp only [B, Pi.add_apply, Pi.sub_apply]
      ring
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary' (HasDerivAt.continuousOn hf)
      (fun s hs => (hf s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (B' := fun s => (z' s + ε) * B s)
      (by dsimp [B]; simp only [sub_self, mul_zero, add_zero, Real.exp_zero, mul_one]; linarith only [hε])
      (HasDerivAt.continuousOn hB) (fun s hs => (hB s (Ico_subset_Icc_self hs)).hasDerivWithinAt) ?_ ht
    intro s hs heq
    have hb := hbound s (Ico_subset_Icc_self hs)
    rw [heq] at hb
    have hpos : 0 < B s := mul_pos (by linarith only [norm_nonneg (f a), hε]) (Real.exp_pos _)
    nlinarith only [hb, mul_pos hε hpos]
  have hcont : ContinuousWithinAt
      (fun ε : ℝ => (‖f a‖ + ε) * Real.exp (z t - z a + ε * (t - a))) (Ioi 0) 0 := by fun_prop
  have H0 := continuousWithinAt_const.closure_le
    (by simp only [closure_Ioi, self_mem_Ici] : (0 : ℝ) ∈ closure (Ioi 0)) hcont H
  simpa only [add_zero, zero_mul] using H0
