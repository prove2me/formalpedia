-- Prove2me | solution 1 for BianchiIX.norm_le_exp_of_norm_deriv_clock_forcing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:55:29.440189+00:00
-- url     : https://prove2.me/submissions/45f40810-4228-483b-b303-ce06ec6c00a9

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


/-- A constant forcing costs only elapsed time when the integrated growth is bounded. -/
theorem solution {f f' : ℝ → E} {z z' : ℝ → ℝ} {a b ε : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hε : 0 ≤ ε) (hclock : ∀ t ∈ Icc a b, z a ≤ z t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ z' t * ‖f t‖ + ε) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ (‖f a‖ + ε * (t - a)) * Real.exp (z t - z a) := by
  intro t ht
  have H : ∀ δ ∈ Ioi (0 : ℝ),
      ‖f t‖ ≤ (‖f a‖ + δ + ε * (t - a)) * Real.exp (z t - z a + δ * (t - a)) := by
    intro δ hδ
    change 0 < δ at hδ
    let B := fun s => (‖f a‖ + δ + ε * (s - a)) * Real.exp (z s - z a + δ * (s - a))
    let B' := fun s => ε * Real.exp (z s - z a + δ * (s - a)) + (z' s + δ) * B s
    have hB (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt B (B' s) s := by
      convert! ((hasDerivAt_const s (‖f a‖ + δ)).add (((hasDerivAt_id' s).sub_const a).const_mul ε)).mul
        ((((hz s hs).sub_const (z a)).add (((hasDerivAt_id' s).sub_const a).const_mul δ)).exp) using 1
      dsimp only [B, B', Pi.add_apply, Pi.sub_apply]
      ring
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary' (HasDerivAt.continuousOn hf)
      (fun s hs => (hf s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (B' := B')
      (by dsimp [B]; simp only [sub_self, mul_zero, add_zero, Real.exp_zero, mul_one]; linarith only [hδ])
      (HasDerivAt.continuousOn hB) (fun s hs => (hB s (Ico_subset_Icc_self hs)).hasDerivWithinAt) ?_ ht
    intro s hs heq
    have hb := hbound s (Ico_subset_Icc_self hs)
    rw [heq] at hb
    have hsa : 0 ≤ s - a := sub_nonneg.mpr hs.1
    have hpos : 0 < B s := mul_pos
      (by linarith only [norm_nonneg (f a), hδ, mul_nonneg hε hsa]) (Real.exp_pos _)
    have he : 1 ≤ Real.exp (z s - z a + δ * (s - a)) := Real.one_le_exp_iff.mpr
      (add_nonneg (sub_nonneg.mpr (hclock s (Ico_subset_Icc_self hs))) (mul_nonneg hδ.le hsa))
    have hforce := mul_le_mul_of_nonneg_left he hε
    dsimp only [B']
    nlinarith only [hb, mul_pos hδ hpos, hforce]
  have hcont : ContinuousWithinAt
      (fun δ : ℝ => (‖f a‖ + δ + ε * (t - a)) * Real.exp (z t - z a + δ * (t - a))) (Ioi 0) 0 := by fun_prop
  have H0 := continuousWithinAt_const.closure_le
    (by simp only [closure_Ioi, self_mem_Ici] : (0 : ℝ) ∈ closure (Ioi 0)) hcont H
  simpa only [add_zero, zero_mul] using H0
