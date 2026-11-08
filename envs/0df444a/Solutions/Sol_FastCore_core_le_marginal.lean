-- Prove2me | solution 1 for FastCore.core_le_marginal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:54:56.997677+00:00
-- url     : https://prove2.me/submissions/d411f780-a99b-4190-b96e-630187eab2af

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsWelfareMaximizing

open ComplementFreeCA.CFRounding (IsAllocation welfare)

open FastCore in
theorem solution {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : InCore b π) {x : Fin n → Finset (Fin m)} (hx : IsWelfareMaximizing b x) (i : Fin n) :
    π i ≤ w b Finset.univ - w b (Finset.univ.erase i) ∧
      w b Finset.univ - w b (Finset.univ.erase i) ≤ b i (x i) := by
  classical
  constructor
  · have h := hπ.2 (Finset.univ.erase i)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    linarith
  · have hN : w b Finset.univ ≤ welfare b x := by
      unfold w
      exact Finset.sup'_le _ _ (fun y hy => hx.2 y (Finset.mem_filter.mp hy).2.1)
    set x' : Fin n → Finset (Fin m) := Function.update x i ∅ with hx'
    have halloc : IsAllocation x' := by
      intro a a' haa'
      by_cases ha : a = i
      · subst ha; simp [x']
      · by_cases ha' : a' = i
        · subst ha'; simp [x']
        · simp only [x', Function.update_of_ne ha, Function.update_of_ne ha']
          exact hx.1 a a' haa'
    have hS : welfare b x' ≤ w b (Finset.univ.erase i) := by
      unfold w
      refine Finset.le_sup' (welfare b) ?_
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, halloc, fun k hk => ?_⟩
      have : k = i := by
        by_contra hne; exact hk (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k⟩)
      subst this; simp [x']
    have hwel : welfare b x = welfare b x' + b i (x i) := by
      unfold welfare
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ (fun k => b k (x' k)) (Finset.mem_univ i)]
      have : ∑ k ∈ Finset.univ.erase i, b k (x k) = ∑ k ∈ Finset.univ.erase i, b k (x' k) :=
        Finset.sum_congr rfl (fun k hk => by
          rw [hx', Function.update_of_ne (Finset.ne_of_mem_erase hk)])
      rw [this]
      simp only [x', Function.update_self, hb.1 i]
      ring
    linarith
