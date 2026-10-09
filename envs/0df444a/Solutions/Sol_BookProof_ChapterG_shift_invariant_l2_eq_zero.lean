-- Prove2me | solution 1 for BookProof.ChapterG.shift_invariant_l2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:17:42.240416+00:00
-- url     : https://prove2.me/submissions/ed48563c-c74f-4827-9b52-c47d3e288a22

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.shift_invariant_l2_eq_zero
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

set_option maxHeartbeats 1000000 in
theorem solution (Ψ : lp (fun _ : ℤ => ℂ) 2)
    (hΨ : ∀ k, Ψ (k + 1) = Ψ k) : Ψ = 0 := by

  have hconst : ∀ k : ℤ, Ψ k = Ψ 0 := by
    intro k
    induction k using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hΨ (n:ℤ)]; exact ih
    | pred n ih =>
      have h := hΨ (-(n:ℤ) - 1)
      rw [sub_add_cancel] at h
      rw [← h]; exact ih
  have hsum : Summable (fun k : ℤ => ‖Ψ k‖ ^ (2:ℝ)) := by
    have h := lp.memℓp Ψ
    rw [memℓp_gen_iff (by norm_num)] at h
    simpa using h
  have htend := hsum.tendsto_cofinite_zero
  have hc : (fun k : ℤ => ‖Ψ k‖ ^ (2:ℝ)) = fun _ => ‖Ψ 0‖ ^ (2:ℝ) := by
    funext k; rw [hconst k]
  rw [hc] at htend
  have hzero : ‖Ψ 0‖ ^ (2:ℝ) = 0 :=
    (tendsto_nhds_unique htend tendsto_const_nhds).symm
  have hn0 : ‖Ψ 0‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num)).mp hzero
  have hΨ0 : Ψ 0 = 0 := by simpa using hn0
  apply lp.ext
  funext k
  simp only [lp.coeFn_zero, Pi.zero_apply]
  rw [hconst k, hΨ0]
