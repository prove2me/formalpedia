-- Prove2me | solution 1 for FairChores.cbar_eq_zero_of_MMS_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:23:52.856657+00:00
-- url     : https://prove2.me/submissions/f63f89e4-4f34-4a17-979d-70c73bb8fb33

import Mathlib
import Definitions.Def_RequestProject_ChoresBagFilling
import Definitions.Def_RequestProject_ChoresMMSApprox
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_cbar_le_price
import Theorems.Thm_FairChores_cbar_nonneg
import Theorems.Thm_FairChores_wtSum_univ_le_nsmul_MMS
import Theorems.Thm_FairChores_wt_nonneg
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t)
    (hn : 0 < n) (h0 : MMS n c p = 0) (t : T) : cbar c p t = 0 := by
  classical
  have hbound := wtSum_univ_le_nsmul_MMS (c := c) (p := p) (n := n) hc hn
  rw [h0] at hbound
  simp only [mul_zero] at hbound
  have hnonneg : ∀ s ∈ (Finset.univ : Finset T), 0 ≤ wt c p 0 s := fun s _ => wt_nonneg hc hp s
  have hzero : wt c p 0 t = 0 := by
    have hsum : ∑ s, wt c p 0 s = 0 :=
      le_antisymm hbound (Finset.sum_nonneg hnonneg)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum t (Finset.mem_univ t)
  by_cases hpos : 0 < cbar c p t
  · exfalso
    rw [wt, if_pos hpos] at hzero
    have := cbar_le_price (c := c) (p := p) t
    rw [hzero] at this
    linarith
  · have := cbar_nonneg hc hp t
    linarith [not_lt.mp hpos]
end FairChores
