-- Prove2me | solution 1 for DecentralizedDistribution.FirstBest.example1_transfer_price_not_in_core
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:16:50.725255+00:00
-- url     : https://prove2.me/submissions/86be739d-a85d-4419-95a9-2dbc88e1fcc1

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System

open Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

theorem aux_ex1tp_profit (sys : System 4 0)
    (hr : ∀ n, sys.r n = 10) (hv : ∀ n, sys.v n = 5)
    (ht : ∀ i n, sys.t i n = 1) (S : Finset (Fin 4)) (q : ShippingPlan 4 0) :
    shippingProfit sys S q = ∑ j ∈ S, ∑ n ∈ S, 4 * q (Sum.inl j) n := by
  have hm : ∀ j n, sys.margin (Sum.inl j) n = 4 := by
    intro j n
    simp only [System.margin, System.salvage, Sum.elim_inl, hr, hv, ht]
    norm_num
  simp [shippingProfit, hm]

end DecentralizedDistribution.FirstBest

open DecentralizedDistribution.FirstBest
open Supermodularity.Cooperative

theorem solution (sys : System 4 0)
    (hr : ∀ n, sys.r n = 10) (hv : ∀ n, sys.v n = 5)
    (ht : ∀ i n, sys.t i n = 1) (hβ : ∀ i n, sys.β i n = 1)
    (Z : Profile 4 0) (hX : (fun n => (Z n).X) = ![3, 1, 0, 0])
    (D : Demand 4) (hD : D = ![0, 0, 5, 2]) :
    coalitionValue sys Finset.univ Z D = 16 ∧
    coalitionValue sys {0, 3} Z D = 8 ∧
    (![0, 0, 16, 0] : Fin 4 → ℝ) ∉ Core Finset.univ (fun S => coalitionValue sys S Z D) := by
  subst hD
  have hXn : ∀ n, (Z n).X = ![3, 1, 0, 0] n := fun n => congrFun hX n
  have hH : ∀ j, residualInv Z ![0, 0, 5, 2] j = ![3, 1, 0, 0] j := by
    intro j
    fin_cases j <;> simp [residualInv, hXn]
  have hE : ∀ n, residualDem Z ![0, 0, 5, 2] n = ![0, 0, 5, 2] n := by
    intro n
    fin_cases n <;> simp [residualDem, hXn]
  have hprof := aux_ex1tp_profit sys hr hv ht
  -- value of the grand coalition
  have h16 : coalitionValue sys Finset.univ Z ![0, 0, 5, 2] = 16 := by
    apply IsGreatest.csSup_eq
    constructor
    · let q : ShippingPlan 4 0 := Sum.elim
        (fun j n => (![![0, 0, 3, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] :
          Fin 4 → Fin 4 → ℝ) j n)
        (fun w => Fin.elim0 w)
      refine ⟨q, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i n
          rcases i with j | w
          · fin_cases j <;> fin_cases n <;> simp [q]
          · exact Fin.elim0 w
        · intro i n h
          rcases i with j | w
          · exact absurd ⟨by simp [LocIn], Finset.mem_univ n⟩ h
          · exact Fin.elim0 w
        · intro i n h
          rw [hβ] at h
          norm_num at h
        · intro j _
          rw [hH]
          fin_cases j <;> simp [q, Fin.sum_univ_four]
        · intro w; exact Fin.elim0 w
        · intro n _
          rw [hE]
          fin_cases n <;> simp [q, Fin.sum_univ_four, hβ] <;> norm_num
      · rw [hprof]
        simp [q, Fin.sum_univ_four]
        norm_num
    · rintro x ⟨q, ⟨_, _, _, h4, _, _⟩, rfl⟩
      rw [hprof]
      have a0 := h4 0 (Finset.mem_univ _)
      have a1 := h4 1 (Finset.mem_univ _)
      have a2 := h4 2 (Finset.mem_univ _)
      have a3 := h4 3 (Finset.mem_univ _)
      simp only [hH, Fin.sum_univ_four] at a0 a1 a2 a3 ⊢
      simp at a0 a1 a2 a3
      linarith
  -- value of the coalition {0, 3}
  have h8 : coalitionValue sys {0, 3} Z ![0, 0, 5, 2] = 8 := by
    apply IsGreatest.csSup_eq
    constructor
    · let q : ShippingPlan 4 0 := Sum.elim
        (fun j n => (![![0, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] :
          Fin 4 → Fin 4 → ℝ) j n)
        (fun w => Fin.elim0 w)
      refine ⟨q, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i n
          rcases i with j | w
          · fin_cases j <;> fin_cases n <;> simp [q]
          · exact Fin.elim0 w
        · intro i n h
          rcases i with j | w
          · fin_cases j <;> fin_cases n <;> simp_all [q, LocIn]
          · exact Fin.elim0 w
        · intro i n h
          rw [hβ] at h
          norm_num at h
        · intro j hj
          rw [hH]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl <;> simp [q] <;> norm_num
        · intro w; exact Fin.elim0 w
        · intro n hn
          rw [hE]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hn
          rcases hn with rfl | rfl <;> simp [q, hβ]
      · rw [hprof]
        simp [q]
        norm_num
    · rintro x ⟨q, ⟨h1, _, _, _, _, h6⟩, rfl⟩
      rw [hprof]
      have b0 := h6 0 (by simp)
      have b3 := h6 3 (by simp)
      have n00 := h1 (Sum.inl 0) 0
      have n30 := h1 (Sum.inl 3) 0
      simp only [hE, hβ, div_one] at b0 b3
      simp at b0 b3 ⊢
      linarith
  refine ⟨h16, h8, ?_⟩
  rintro ⟨_, h2⟩
  have := h2 {0, 3} (Finset.subset_univ _)
  simp only at this
  rw [h8] at this
  simp at this
  norm_num at this
