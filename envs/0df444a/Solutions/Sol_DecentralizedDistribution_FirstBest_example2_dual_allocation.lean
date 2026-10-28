-- Prove2me | solution 1 for DecentralizedDistribution.FirstBest.example2_dual_allocation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T01:05:07.607945+00:00
-- url     : https://prove2.me/submissions/ce59fc81-da45-4fde-9da8-5c8e894b75e3

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices

open Supermodularity.Cooperative

namespace Aux_DDFBex2
open DecentralizedDistribution.FirstBest

variable (sys : System 4 0) (Z : Profile 4 0) (D : Demand 4)

lemma profit_eq (hr : ∀ n, sys.r n = 10) (hv : ∀ n, sys.v n = 5) (ht : ∀ i n, sys.t i n = 1)
    (S : Finset (Fin 4)) (q : ShippingPlan 4 0) :
    shippingProfit sys S q = 4 * ∑ j ∈ S, ∑ n ∈ S, q (Sum.inl j) n := by
  simp only [shippingProfit, System.margin, System.salvage, Sum.elim_inl, hr, hv, ht,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro n _
  ring

lemma bounds (hβ : ∀ i n, sys.β i n = 1) (S : Finset (Fin 4)) (q : ShippingPlan 4 0)
    (hq : IsFeasibleShipping sys S Z D q) :
    (∑ j ∈ S, ∑ n ∈ S, q (Sum.inl j) n ≤ ∑ j ∈ S, residualInv Z D j) ∧
    (∑ j ∈ S, ∑ n ∈ S, q (Sum.inl j) n ≤ ∑ n ∈ S, residualDem Z D n) := by
  obtain ⟨_, _, _, h4, _, h6⟩ := hq
  constructor
  · exact Finset.sum_le_sum (fun j hj => h4 j hj)
  · rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n hn
    have := h6 n hn
    simp only [hβ, div_one, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at this
    exact this

lemma zero_feas (S : Finset (Fin 4)) :
    IsFeasibleShipping sys S Z D (fun _ _ => 0) := by
  refine ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro j _; simp [residualInv]
  · intro w; exact Fin.elim0 w
  · intro n _; simp [residualDem]

end Aux_DDFBex2

open DecentralizedDistribution.FirstBest Aux_DDFBex2 in
theorem solution (sys : System 4 0)
    (hr : ∀ n, sys.r n = 10) (hv : ∀ n, sys.v n = 5)
    (ht : ∀ i n, sys.t i n = 1) (hβ : ∀ i n, sys.β i n = 1)
    (Z : Profile 4 0) (hX : (fun n => (Z n).X) = ![2, 2, 2, 0])
    (D : Demand 4) (hD : D = ![0, 0, 0, 10]) :
    coalitionValue sys Finset.univ Z D = 24 ∧
    (∃ p, IsOptimalDual sys Z D p) ∧
    (∀ p, IsOptimalDual sys Z D p → dualAllocation Z D p = ![8, 8, 8, 0]) ∧
    (![0, 0, 0, 24] : Fin 4 → ℝ) ∈ Core Finset.univ (fun S => coalitionValue sys S Z D) := by
  have hXn : ∀ n, (Z n).X = ![2, 2, 2, 0] n := fun n => congrFun hX n
  have hinv : ∀ n, residualInv Z D n = ![2, 2, 2, 0] n := by
    intro n; fin_cases n <;> simp [residualInv, hXn, hD] <;> norm_num
  have hdem : ∀ n, residualDem Z D n = ![0, 0, 0, 10] n := by
    intro n; fin_cases n <;> simp [residualDem, hXn, hD] <;> norm_num
  have hmargin : ∀ j n, sys.margin (Sum.inl j) n = 4 := by
    intro j n; simp only [System.margin, System.salvage, Sum.elim_inl, hr, hv, ht]; norm_num
  have hinvS : ∀ S : Finset (Fin 4), ∑ j ∈ S, residualInv Z D j ≤ 6 := by
    intro S
    calc ∑ j ∈ S, residualInv Z D j ≤ ∑ j, residualInv Z D j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => by simp [residualInv])
      _ = 6 := by simp [Fin.sum_univ_four, hinv]; norm_num
  have hdemS : ∀ S : Finset (Fin 4), (3 : Fin 4) ∉ S → ∑ n ∈ S, residualDem Z D n = 0 := by
    intro S h3
    apply Finset.sum_eq_zero
    intro n hn
    have : n ≠ 3 := fun h => h3 (h ▸ hn)
    rw [hdem]
    fin_cases n <;> simp_all
  -- upper bound on coalition values
  have hval_le : ∀ S : Finset (Fin 4), ∀ x ∈ shippingProfit sys S '' {q | IsFeasibleShipping sys S Z D q},
      x ≤ 24 ∧ ((3 : Fin 4) ∉ S → x ≤ 0) := by
    rintro S _ ⟨q, hq, rfl⟩
    obtain ⟨b1, b2⟩ := bounds sys Z D hβ S q hq
    rw [profit_eq sys hr hv ht]
    refine ⟨by linarith [hinvS S], fun h3 => by rw [hdemS S h3] at b2; linarith⟩
  have hne : ∀ S : Finset (Fin 4),
      (shippingProfit sys S '' {q | IsFeasibleShipping sys S Z D q}).Nonempty :=
    fun S => ⟨_, ⟨_, zero_feas sys Z D S, rfl⟩⟩
  -- the optimal plan for the grand coalition
  set qs : ShippingPlan 4 0 := fun i n =>
    Sum.elim (fun j => if n = 3 ∧ j ≠ 3 then (2 : ℝ) else 0) (fun _ => 0) i with hqs
  have hqs_feas : IsFeasibleShipping sys Finset.univ Z D qs := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i n
      rcases i with j | w
      · simp only [hqs, Sum.elim_inl]; split_ifs <;> norm_num
      · exact Fin.elim0 w
    · intro i n h
      rcases i with j | w
      · exact absurd ⟨Finset.mem_univ j, Finset.mem_univ n⟩ h
      · exact Fin.elim0 w
    · intro i n h; rw [hβ] at h; norm_num at h
    · intro j _
      rw [hinv]
      fin_cases j <;> simp [hqs, Fin.sum_univ_four]
    · intro w; exact Fin.elim0 w
    · intro n _
      rw [hdem]
      fin_cases n <;> simp [hqs, Fin.sum_univ_four, hβ] <;> norm_num
  have hqs_val : shippingProfit sys Finset.univ qs = 24 := by
    rw [profit_eq sys hr hv ht]
    simp [hqs, Fin.sum_univ_four]
    norm_num
  have hv24 : coalitionValue sys Finset.univ Z D = 24 := by
    apply IsGreatest.csSup_eq
    exact ⟨⟨qs, hqs_feas, hqs_val⟩, fun x hx => (hval_le _ x hx).1⟩
  -- dual
  have hobj : ∀ p : DualPrices 4 0, dualObjective Z D p =
      2 * p.1 0 + 2 * p.1 1 + 2 * p.1 2 + 10 * p.2.2 3 := by
    intro p
    simp [dualObjective, Fin.sum_univ_four, hinv, hdem]
    ring
  have hlow : ∀ p : DualPrices 4 0, IsDualFeasible sys p →
      ∀ j : Fin 4, 4 ≤ p.1 j + p.2.2 3 := by
    intro p hp j
    have := hp.2.2.2.1 j 3
    simp only [hβ, hmargin] at this
    linarith
  set ps : DualPrices 4 0 := (fun _ => 4, fun _ => 0, fun _ => 0) with hps
  have hps_feas : IsDualFeasible sys ps := by
    refine ⟨fun _ => by norm_num, fun _ => le_rfl, fun _ => le_rfl, ?_, ?_⟩
    · intro j n; simp only [hβ, hmargin]; norm_num
    · intro w; exact Fin.elim0 w
  have hps_obj : dualObjective Z D ps = 24 := by rw [hobj]; norm_num
  have hps_opt : IsOptimalDual sys Z D ps := by
    refine ⟨hps_feas, fun p' hp' => ?_⟩
    rw [hps_obj, hobj]
    have h0 := hlow p' hp' 0
    have h1 := hlow p' hp' 1
    have h2 := hlow p' hp' 2
    have h3 := hp'.2.2.1 3
    linarith
  refine ⟨hv24, ⟨ps, hps_opt⟩, ?_, ?_⟩
  · intro p hp
    have hle := hp.2 ps hps_feas
    rw [hps_obj, hobj] at hle
    have h0 := hlow p hp.1 0
    have h1 := hlow p hp.1 1
    have h2 := hlow p hp.1 2
    have h3 := hp.1.2.2.1 3
    have e3 : p.2.2 3 = 0 := by linarith
    have e0 : p.1 0 = 4 := by linarith
    have e1 : p.1 1 = 4 := by linarith
    have e2 : p.1 2 = 4 := by linarith
    funext n
    fin_cases n <;> simp [dualAllocation, hinv, hdem, e0, e1, e2, e3] <;> norm_num
  · refine ⟨?_, ?_⟩
    · show _ = coalitionValue sys Finset.univ Z D
      rw [hv24]; simp [Fin.sum_univ_four]
    · intro S _
      apply csSup_le (hne S)
      intro x hx
      obtain ⟨h24, h0⟩ := hval_le S x hx
      by_cases h3 : (3 : Fin 4) ∈ S
      · have : ∑ i ∈ S, (![0, 0, 0, 24] : Fin 4 → ℝ) i = 24 := by
          rw [Finset.sum_eq_single_of_mem 3 h3]
          · simp
          · intro i _ hi; fin_cases i <;> simp_all
        rw [this]; exact h24
      · have : ∑ i ∈ S, (![0, 0, 0, 24] : Fin 4 → ℝ) i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have : i ≠ 3 := fun h => h3 (h ▸ hi)
          fin_cases i <;> simp_all
        rw [this]; exact h0 h3
