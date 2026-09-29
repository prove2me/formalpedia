-- Prove2me | solution 1 for CalibratedCE.Convergence.empDist_isJointDist
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:21:14.359603+00:00
-- url     : https://prove2.me/submissions/ab5e255a-65d9-419a-b91a-525c40c8b343

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Convergence_EmpDist

open CalibratedCE.Convergence

theorem solution {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ) (ht : 0 < t) :
    IsJointDist (empDist x y t) := by
  classical
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  refine ⟨fun a b => ?_, ?_⟩
  · simp only [empDist]
    positivity
  · -- the fibres of `s ↦ (x s, y s)` partition `range t`
    have hfib : (Finset.range t).card
        = ∑ q ∈ (Finset.univ : Finset (Fin m × Fin n)),
            ((Finset.range t).filter (fun s => (x s, y s) = q)).card :=
      Finset.card_eq_sum_card_fiberwise (fun s _ => Finset.mem_univ _)
    have hsplit : ∑ q ∈ (Finset.univ : Finset (Fin m × Fin n)),
          ((Finset.range t).filter (fun s => (x s, y s) = q)).card
        = ∑ a, ∑ b, ((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      apply Finset.filter_congr
      intro s _
      simp [Prod.ext_iff]
    have hcount : ∑ a, ∑ b, (((Finset.range t).filter
        (fun s => x s = a ∧ y s = b)).card : ℝ) = (t : ℝ) := by
      have := hfib.trans hsplit
      rw [Finset.card_range] at this
      have hc : ((∑ a, ∑ b, ((Finset.range t).filter
          (fun s => x s = a ∧ y s = b)).card : ℕ) : ℝ) = (t : ℝ) := by
        exact_mod_cast this.symm
      push_cast at hc
      exact hc
    simp only [empDist]
    rw [show (∑ a, ∑ b, (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ)
        / (t : ℝ)) = (∑ a, ∑ b, (((Finset.range t).filter
        (fun s => x s = a ∧ y s = b)).card : ℝ)) / (t : ℝ) by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div]]
    rw [hcount, div_self (ne_of_gt htR)]
