-- Prove2me | solution 1 for ConsistentSubmodular.CompatibleProfile.triangular_baseline_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:29.618345+00:00
-- url     : https://prove2.me/submissions/17a85495-c1df-447d-a113-8d2ad2dc2cc6

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Triangularization

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace CompatibleProfile

variable {d : ℕ} (P : CompatibleProfile d)

/-- Each baseline increment pays for the full expiring pool. -/
theorem pool_total_le_baseline_increment (t : ℕ) :
    P.poolValue t Finset.univ ≤ P.baseline (t + 1) - P.baseline t := by
  apply finiteMaximum_le
  · exact sub_nonneg.mpr (P.values_increase t (t + 1) (Nat.le_succ t) ∅)
  · intro i _
    have h := P.values_increase t (t + 1) (Nat.le_succ t) {i}
    dsimp [loss, residual, residualOn, baseline]
    linarith

end CompatibleProfile

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

theorem fin_before_step {m : ℕ} (a : Fin (m + 1) → ℝ) (t : Fin m) :
    (∑ j, if j < t.succ then a j else 0) =
      (∑ j, if j < t.castSucc then a j else 0) + a t.castSucc := by
  have hpoint (j : Fin (m + 1)) :
      (if j < t.succ then a j else 0) =
        (if j < t.castSucc then a j else 0) + (if j = t.castSucc then a j else 0) := by
    by_cases heq : j = t.castSucc
    · subst j
      simp
    · have hiff : j < t.succ ↔ j < t.castSucc := by
        have hne : j.val ≠ t.val := by intro h; exact heq (Fin.ext h)
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega
      simp [heq, hiff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))

theorem triangular_pool_le_raw (I : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    finiteMaximum I (fun i => P.triangularLength i j) ≤
      finiteMaximum I (fun i => P.rawLength i j) := by
  apply finiteMaximum_le (finiteMaximum_nonnegative (fun i _ => P.rawLength_nonnegative i j))
  exact fun i hi => (P.triangularLength_le_raw i j).trans
    (le_finiteMaximum (g := fun i => P.rawLength i j) hi)

end CompatibleProfile

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.CompatibleProfile
variable {m : ℕ} (P : CompatibleProfile (m + 1))

theorem solution (t : Fin (m + 1)) :
    (∑ j, if j < t then finiteMaximum Finset.univ (fun i => P.triangularLength i j) else 0) ≤
      P.baseline t.val := by
  induction t using Fin.induction with
  | zero => simpa [baseline] using (P.objective 0).nonnegative ∅
  | succ t ih =>
    rw [fin_before_step]
    have hraw : finiteMaximum Finset.univ (fun i => P.rawLength i t.castSucc) =
        P.poolValue t.val Finset.univ := by
      simp only [rawLength, Fin.castSucc_ne_last, ite_false, Fin.val_castSucc, poolValue]
    have htri := P.triangular_pool_le_raw Finset.univ t.castSucc
    rw [hraw] at htri
    have hpay := P.pool_total_le_baseline_increment t.val
    simp only [Fin.val_castSucc, Fin.val_succ] at *
    linarith

end
