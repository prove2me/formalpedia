-- Prove2me | solution 1 for BookProof.ChapterGaugeShiftExample.shiftOp_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:37:28.957919+00:00
-- url     : https://prove2.me/submissions/a26d00e4-81a4-42e1-a142-1e4d651ed27a

-- Generated from ChapterGaugeShiftExample.lean — solution of BookProof.ChapterGaugeShiftExample.shiftOp_eq_self_iff
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
open BookProof.ChapterGaugeShiftExample



open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution {m : ℤ} (hm : m ≠ 0) {f : L2Z} (hf : shiftOp m f = f) :
    f = 0 := by

  have hper : ∀ (n : ℤ) (k : ℤ), (f : ℤ → ℂ) (k + n * m) = (f : ℤ → ℂ) k := by
    have hstep : ∀ k : ℤ, (f : ℤ → ℂ) (k + m) = (f : ℤ → ℂ) k := by
      intro k
      have := congrArg (fun v : L2Z => (v : ℤ → ℂ) k) hf
      simpa using this
    intro n
    induction n using Int.induction_on with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      have : k + ((j : ℤ) + 1) * m = (k + j * m) + m := by ring
      rw [this, hstep (k + j * m), ih k]
    | pred j ih =>
      intro k
      have h1 : k + (-(j : ℤ) - 1) * m + m = k + (-(j : ℤ)) * m := by ring
      have h2 := hstep (k + (-(j : ℤ) - 1) * m)
      rw [h1] at h2
      rw [← h2, ih k]
  have hsum := summable_normSq f
  apply lp.ext
  funext k
  simp only [lp.coeFn_zero, Pi.zero_apply]
  -- the constant subfamily along the arithmetic progression `k + n * m`
  have hinj : Function.Injective (fun n : ℤ => k + n * m) := by
    intro a b hab
    simp only at hab
    have : a * m = b * m := by omega
    exact mul_right_cancel₀ hm this
  have hsub : Summable fun n : ℤ => ‖(f : ℤ → ℂ) (k + n * m)‖ ^ 2 :=
    hsum.comp_injective hinj
  have hconst : (fun n : ℤ => ‖(f : ℤ → ℂ) (k + n * m)‖ ^ 2)
      = fun _ : ℤ => ‖(f : ℤ → ℂ) k‖ ^ 2 := by
    funext n; rw [hper n k]
  rw [hconst] at hsub
  have htend := hsub.tendsto_cofinite_zero
  have hzero : ‖(f : ℤ → ℂ) k‖ ^ 2 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds htend
  have hnk : ‖(f : ℤ → ℂ) k‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hzero
  simpa using hnk
