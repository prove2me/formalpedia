-- Prove2me | solution 1 for BianchiIX.abs_le_affine_exp_of_clock_damping
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:57:55.983552+00:00
-- url     : https://prove2.me/submissions/ea1b652a-7aba-40a0-9e38-fa6ed1fa8e1d

import Theorems.Thm_BianchiIX_abs_le_primitive_of_damping
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


/-- Exponentially decaying forcing with the same damping rate, in any nondecreasing clock. -/
theorem solution {f d g z z' : ℝ → ℝ} {a b c B : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (z' t * (d t * f t + g t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzpos : ∀ t ∈ Icc a b, 0 ≤ z' t)
    (hd : ∀ t ∈ Icc a b, d t ≤ -c)
    (hg : ∀ t ∈ Icc a b, |g t| ≤ B * Real.exp (-c * (z t - z a))) :
    ∀ t ∈ Icc a b, |f t| ≤ Real.exp (-c * (z t - z a)) * (|f a| + B * (z t - z a)) := by
  let e := fun t => Real.exp (c * (z t - z a))
  let F := fun t => e t * f t
  let D := fun t => z' t * (d t + c)
  let G := fun t => e t * z' t * g t
  let p := fun t => B * z t
  have he (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt e (e t * (c * z' t)) t := by
    convert! (((hz t ht).sub_const (z a)).const_mul c).exp using 1
  have hF (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt F (D t * F t + G t) t := by
    convert! (he t ht).mul (hf t ht) using 1
    dsimp [D, F, G]
    ring
  have hG (t : ℝ) (ht : t ∈ Icc a b) : |G t| ≤ B * z' t := by
    have hcancel : e t * Real.exp (-c * (z t - z a)) = 1 := by
      dsimp only [e]
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      |G t| = e t * z' t * |g t| := by
        dsimp [G]
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hzpos t ht)]
      _ ≤ e t * z' t * (B * Real.exp (-c * (z t - z a))) :=
        mul_le_mul_of_nonneg_left (hg t ht) (mul_nonneg (Real.exp_pos _).le (hzpos t ht))
      _ = B * z' t := by
        calc
          _ = B * z' t * (e t * Real.exp (-c * (z t - z a))) := by ring
          _ = _ := by rw [hcancel, mul_one]
  have H := abs_le_primitive_of_damping
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => hF t (Ico_subset_Icc_self ht))
    (fun t ht => ((hz t ht).const_mul B).continuousAt.continuousWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).const_mul B)
    (fun t ht => mul_nonpos_of_nonneg_of_nonpos (hzpos t (Ico_subset_Icc_self ht))
      (by linarith only [hd t (Ico_subset_Icc_self ht)]))
    (fun t ht => hG t (Ico_subset_Icc_self ht))
  intro t ht
  have H' := H t ht
  change |F t| ≤ |F a| + (p t - p a) at H'
  have hFa : F a = f a := by simp [F, e]
  rw [hFa] at H'
  have hFt : |F t| = e t * |f t| := by dsimp only [F]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [hFt] at H'
  have hcancel : Real.exp (-c * (z t - z a)) * e t = 1 := by
    dsimp only [e]
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have H'' := mul_le_mul_of_nonneg_left H' (Real.exp_pos (-c * (z t - z a))).le
  rw [← mul_assoc, hcancel, one_mul] at H''
  convert! H'' using 1
  dsimp [p]
  ring
