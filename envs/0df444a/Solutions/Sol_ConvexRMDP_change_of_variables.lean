-- Prove2me | solution 1 for ConvexRMDP.change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:14:26.979991+00:00
-- url     : https://prove2.me/submissions/52d4947b-9fcb-445d-a66e-9724a058293c

import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_RMDP_tOp
import Theorems.Thm_ConvexRMDP_decomposition_4_5
import Theorems.Thm_ConvexRMDP_lemma_4_2

open ConvexRMDP

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    (∀ v : S → ℝ, v ≤ M.regOp b v ↔
        (fun s => expB b (v s)) ≤ M.tOp b (fun s => expB b (v s))) ∧
      Convex ℝ {x : S → ℝ | (∀ s, 0 < x s) ∧ x ≤ M.tOp b x} := by
  have hdecomp := decomposition_4_5 M b hb
  refine ⟨fun v => ?_, ?_⟩
  · let x : S → ℝ := fun s => expB b (v s)
    have hx_pos : ∀ s, 0 < x s := fun s => Real.exp_pos (b * v s)
    constructor
    · intro hv s
      have hvs : v s ≤ logB b (M.tOp b x s) := by
        have h1 := hv s
        rwa [congr_fun (hdecomp.1 v) s] at h1
      unfold logB at hvs
      have hbv : b * v s ≤ Real.log (M.tOp b x s) := by
        rw [le_div_iff₀ hb] at hvs
        linarith
      calc expB b (v s)
          = Real.exp (b * v s) := rfl
        _ ≤ Real.exp (Real.log (M.tOp b x s)) := Real.exp_le_exp.mpr hbv
        _ = M.tOp b x s := Real.exp_log (hdecomp.2 x hx_pos s)
    · intro hx s
      rw [congr_fun (hdecomp.1 v) s]
      unfold logB
      rw [le_div_iff₀ hb]
      have hxs : Real.exp (b * v s) ≤ M.tOp b x s := hx s
      have hlog := Real.log_le_log (Real.exp_pos (b * v s)) hxs
      rw [Real.log_exp] at hlog
      linarith
  · intro x hx y hy α β hα hβ hαβ
    have hx_pi : x ∈ Set.pi Set.univ fun _ : S => Set.Ioi (0 : ℝ) := fun s _ => hx.1 s
    have hy_pi : y ∈ Set.pi Set.univ fun _ : S => Set.Ioi (0 : ℝ) := fun s _ => hy.1 s
    refine ⟨fun s => ?_, fun s => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hα0 : α = 0
      · have hβ1 : β = 1 := by linarith
        simp [hα0, hβ1, hy.1 s]
      · have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        exact add_pos_of_pos_of_nonneg (mul_pos hα_pos (hx.1 s)) (mul_nonneg hβ (hy.1 s).le)
    · have hconc := (lemma_4_2 M b hb s).2 hx_pi hy_pi hα hβ hαβ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hconc ⊢
      have hlin : α * x s + β * y s ≤ α * M.tOp b x s + β * M.tOp b y s :=
        add_le_add (mul_le_mul_of_nonneg_left (hx.2 s) hα) (mul_le_mul_of_nonneg_left (hy.2 s) hβ)
      exact hlin.trans hconc
