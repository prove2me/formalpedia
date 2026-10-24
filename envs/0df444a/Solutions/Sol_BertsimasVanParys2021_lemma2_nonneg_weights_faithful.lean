-- Prove2me | solution 1 for BertsimasVanParys2021.lemma2_nonneg_weights_faithful
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T22:44:29.058504+00:00
-- url     : https://prove2.me/submissions/1fc9c479-2131-41f4-9a1f-71b0dfdb3eff

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

open BootRobust.NWDual in
theorem solution :
    ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ)
      (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwD : 0 < ∑ i, w i * D i)
      {Z : Type} (L : Z → ι → ℝ) (hL : ∀ z i, 0 ≤ L z i) (z : Z),
      robustNW BootRobust.Perf.bootDist D r w (L z) =
        ⨅ α ∈ dualSet D r w (L z), (α : EReal)) := by
  intro h
  -- counterexample: two points, D = (1/2, 1/2), w = (1, 0), losses 0, radius r = 1
  have hD : (fun _ : Fin 2 => (1 / 2 : ℝ)) ∈ stdSimplex ℝ (Fin 2) := by
    refine ⟨fun _ => by norm_num, ?_⟩
    simp
  have H := h (ι := Fin 2) (fun _ => 1 / 2) hD 1 (fun i => if i = 0 then 1 else 0)
    (fun i => by split_ifs <;> norm_num) (by simp) (Z := Unit)
    (fun _ _ => 0) (fun _ _ => le_refl _) ()
  -- the dual feasible set is empty
  have hempty : dualSet (fun _ : Fin 2 => (1 / 2 : ℝ)) 1 (fun i => if i = 0 then 1 else 0)
      (fun _ => 0) = ∅ := by
    ext α
    simp only [dualSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
      not_and, not_le]
    intro ν hν
    simp only [Fin.sum_univ_two]
    have key : ∀ x : ℝ, 0 < ν * Real.log (Real.exp x * (1 / 2) + Real.exp (((0 - α) * if (1 : Fin 2) = 0 then 1 else 0) / ν) * (1 / 2)) + 1 * ν := by
      intro x
      have he : 0 < Real.exp x := Real.exp_pos _
      simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, mul_zero, zero_div,
        Real.exp_zero, one_mul]
      have hS : (1 / 2 : ℝ) < Real.exp x * (1 / 2) + 1 / 2 := by nlinarith
      have hlog : Real.log (1 / 2) < Real.log (Real.exp x * (1 / 2) + 1 / 2) :=
        Real.log_lt_log (by norm_num) hS
      have hl2 : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
        rw [one_div, Real.log_inv]
      have h2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      nlinarith
    exact key _
  rw [hempty] at H
  simp only [Set.mem_empty_iff_false, iInf_false, iInf_top] at H
  -- the primal value is at most 0
  have hle : robustNW BootRobust.Perf.bootDist (fun _ : Fin 2 => (1 / 2 : ℝ)) 1
      (fun i => if i = 0 then 1 else 0) (fun _ => 0) ≤ 0 := by
    unfold robustNW
    refine iSup₂_le fun D' _ => ?_
    simp [BootRobust.Perf.nwEst]
  rw [H] at hle
  exact absurd hle (by simp)
