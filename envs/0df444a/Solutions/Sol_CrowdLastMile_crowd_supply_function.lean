-- Prove2me | solution 1 for CrowdLastMile.crowd_supply_function
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:11:12.179671+00:00
-- url     : https://prove2.me/submissions/151fafe1-956f-494b-9fd7-1513ea6ea3a9

import Mathlib
import Definitions.Def_CrowdLastMile_ClosedForms

open Finset

open CrowdLastMile in
theorem solution (p : Params) (hV : p.Valid) (P : ℝ) (hP : 0 < P) :
    (∀ w : ℝ, p.Participation P w ↔ p.wSupply P ≤ w) ∧
    StrictMono (fun w : ℝ => p.obj P w) ∧
    (0 < p.R → 0 < p.wSupply P) := by
  have hm : (1:ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.one_le_m
  have hq : (1:ℝ) ≤ (p.q : ℝ) := by exact_mod_cast p.hq
  have hNr : (1:ℝ) ≤ (p.N : ℝ) := by exact_mod_cast p.hN
  have hNpos : (0:ℝ) < (p.N : ℝ) := by linarith
  have hmq : 1 ≤ p.m * p.q := Nat.mul_pos p.one_le_m p.hq
  have hne1 : (Icc 1 (p.m * p.q)).Nonempty := nonempty_Icc.mpr hmq
  have hneM : (Icc 1 p.m).Nonempty := p.Icc_one_m_nonempty
  have hsβ : 0 < ∑ i ∈ Icc 1 p.m, p.β * Real.sqrt ((p.q : ℝ) + 1) / p.v i :=
    Finset.sum_pos (fun i hi => div_pos (mul_pos hV.β_pos (Real.sqrt_pos.mpr (by linarith)))
      (hV.v_pos i hi)) hneM
  have hC2 : 0 < p.C2 := by
    unfold Params.C2
    exact div_pos (Finset.sum_pos (fun i hi => hV.μa_pos i hi) hne1) (by linarith)
  have hC1 : 0 < p.C1 := by
    unfold Params.C1
    have h0 : 0 ≤ (∑ i ∈ Icc 1 (p.m * p.q), p.μs i) / (p.m : ℝ) :=
      div_nonneg (Finset.sum_nonneg (fun i hi => hV.μs_nonneg i hi)) (by linarith)
    have := div_pos hsβ (by linarith : (0:ℝ) < p.m)
    linarith
  have hidx : ∀ j ∈ Icc 1 p.N, ∀ i ∈ Icc 1 p.τm,
      ∀ k ∈ Icc ((p.jIdx j i - 1) * p.q + 1) (p.jIdx j i * p.q), k ∈ Icc 1 (p.m * p.q) := by
    intro j hj i hi k hk
    rw [mem_Icc] at hj hi hk ⊢
    have h1 : (i - 1) * p.N + j ≤ p.τm * p.N := by
      calc (i - 1) * p.N + j ≤ (i - 1) * p.N + p.N := by omega
        _ = i * p.N := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hi.1]
        _ ≤ p.τm * p.N := Nat.mul_le_mul_right _ hi.2
    have h2 : p.jIdx j i * p.q ≤ p.m * p.q := by
      unfold Params.jIdx Params.m
      exact Nat.mul_le_mul_right _ h1
    exact ⟨by omega, le_trans hk.2 h2⟩
  have hC : 0 < p.C := by
    unfold Params.C
    apply div_pos
    · have h2 : 0 ≤ ∑ j ∈ Icc 1 p.N,
          ((∑ i ∈ Icc 1 p.τm, ∑ k ∈ Icc ((p.jIdx j i - 1) * p.q + 1) (p.jIdx j i * p.q), p.μs k)
            + p.γs * Real.sqrt
                (∑ i ∈ Icc 1 p.τm,
                  ∑ k ∈ Icc ((p.jIdx j i - 1) * p.q + 1) (p.jIdx j i * p.q), (p.σs k) ^ 2)) :=
        Finset.sum_nonneg (fun j hj => add_nonneg
          (Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun k hk =>
            hV.μs_nonneg k (hidx j hj i hi k hk))))
          (mul_nonneg hV.γs_nonneg (Real.sqrt_nonneg _)))
      linarith
    · exact mul_pos (by linarith) (by linarith)
  refine ⟨fun w => ?_, ?_, fun hR => ?_⟩
  · unfold Params.Participation Params.wSupply
    rw [ge_iff_le, div_le_div_iff₀ hNpos (mul_pos hNpos hC2), div_le_iff₀ (mul_pos hP hC1)]
    constructor <;> intro h <;> nlinarith
  · intro w1 w2 hw
    unfold Params.obj
    have := mul_lt_mul_of_pos_left hw (mul_pos hP hC)
    linarith
  · unfold Params.wSupply
    exact div_pos (mul_pos hR hC2) (mul_pos hP hC1)
