-- Prove2me | solution 1 for C6BipartiteDomination.paper9_single_repair_resource_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:19.807618+00:00
-- url     : https://prove2.me/submissions/3c6c774c-0e86-4201-8a91-24fff27ac8fe

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_paper9_sCharge_add_xCharge_le_three
import Theorems.Thm_C6BipartiteDomination_paper9_shared_external_charge_eq_four
import Theorems.Thm_C6BipartiteDomination_lemma_8_5_compensation_lower_bound
import Theorems.Thm_C6BipartiteDomination_mem_supportX


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u w : V} (huB : u ∈ BPart G D) (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0)
    (hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u)
    (hk : kCharge G D w = 3 ∨ kCharge G D w = 4) :
    (kCharge G D w = 3 ∧
      vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ≥ 4) ∨
    (kCharge G D w = 4 ∧
      vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ≥ 8) := by
  classical
  let L := sharedCompensation G D (supportX G D w) u
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax huB
  have hC : 11 * (xCharge G D u : ℤ) ≤ vertexCharge G D u := by
    have hbudgetZ : (degreeTo G (SPart G D) u : ℤ) +
        (xCharge G D u : ℤ) ≤ 3 := by
      exact_mod_cast hbudget
    unfold vertexCharge at hbudgetZ ⊢
    omega
  have hsum : (∑ q ∈ L, externalCharge G D q) =
      4 * (L.card : ℤ) := by
    calc
      _ = ∑ q ∈ L, (4 : ℤ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact paper9_shared_external_charge_eq_four G hX huB (by simpa [L] using hq)
      _ = 4 * (L.card : ℤ) := by simp; ring
  have hbound := lemma_8_5_compensation_lower_bound G hCan hmax hw ha hChosen
  have hbound' : kCharge G D w - 2 ≤ xCharge G D u + L.card := by
    simpa [L] using hbound
  rcases hk with hk3 | hk4
  · left
    refine ⟨hk3, ?_⟩
    by_cases hx0 : xCharge G D u = 0
    · have hL : 1 ≤ L.card := by rw [hk3] at hbound'; rw [hx0] at hbound'; omega
      rw [hsum]
      have hC0 : 0 ≤ vertexCharge G D u := by omega
      have hLZ : 1 ≤ (L.card : ℤ) := by exact_mod_cast hL
      have hsum4 : 4 ≤ 4 * (L.card : ℤ) := by nlinarith
      omega
    · have hxpos : 1 ≤ xCharge G D u := by omega
      have hsumNonneg : 0 ≤ ∑ q ∈ L, externalCharge G D q := by rw [hsum]; positivity
      nlinarith [hC, hsumNonneg, hxpos]
  · right
    refine ⟨hk4, ?_⟩
    by_cases hx0 : xCharge G D u = 0
    · have hL : 2 ≤ L.card := by rw [hk4] at hbound'; rw [hx0] at hbound'; omega
      rw [hsum]
      have hC0 : 0 ≤ vertexCharge G D u := by omega
      have hLZ : 2 ≤ (L.card : ℤ) := by exact_mod_cast hL
      have hsum8 : 8 ≤ 4 * (L.card : ℤ) := by nlinarith
      omega
    · have hxpos : 1 ≤ xCharge G D u := by omega
      have hsumNonneg : 0 ≤ ∑ q ∈ L, externalCharge G D q := by rw [hsum]; positivity
      nlinarith [hC, hsumNonneg, hxpos]
end C6BipartiteDomination
