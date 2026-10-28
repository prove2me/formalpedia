-- Prove2me | solution 1 for DisplayMNL.Rounding.revenue_insert
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:23:45.423888+00:00
-- url     : https://prove2.me/submissions/6606d1cb-d3e8-4254-8108-ffbed5d889fe

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

open DisplayMNL.Rounding in
theorem solution {n : ℕ} (I : Instance n) (hr : ∀ i, 0 < I.r i) (hw : ∀ i, 0 < I.w i)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    rev I (insert i S) =
      rev I S * ((1 + wt I S) / (1 + wt I S + I.w i)) + I.r i * (I.w i / (1 + wt I S + I.w i)) := by
  have hS : 0 ≤ wt I S := Finset.sum_nonneg (fun j _ => (hw j).le)
  have hwi := hw i
  have h1 : (1 + wt I S) ≠ 0 := by positivity
  have h2 : (1 + wt I S + I.w i) ≠ 0 := by positivity
  have e1 : rhoSet I (insert i S) = rho I i + rhoSet I S := by
    unfold rhoSet; rw [Finset.sum_insert hi]
  have e2 : wt I (insert i S) = I.w i + wt I S := by
    unfold wt; rw [Finset.sum_insert hi]
  unfold rev
  rw [e1, e2]
  have e3 : rho I i = I.r i * I.w i := rfl
  rw [e3]
  have h3 : (1 + (I.w i + wt I S)) = 1 + wt I S + I.w i := by ring
  rw [h3]
  field_simp
  ring
