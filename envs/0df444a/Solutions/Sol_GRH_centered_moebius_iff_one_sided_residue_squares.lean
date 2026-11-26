-- Prove2me | solution 1 for GRH.centered_moebius_iff_one_sided_residue_squares
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T20:57:57.205891+00:00
-- url     : https://prove2.me/submissions/ee54ee24-4b20-4f98-a25f-5407bc8e90b0

import Theorems.Thm_GRH_riemannHypothesis_iff_upper_mertens_at_squares
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
import Theorems.Thm_GRH_reduced_moebius_principal_bounds_of_dirichlet_prefixes
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound
import Mathlib.Tactic.Linarith

open Finset GRH.OneSidedMoebius

private theorem ordinaryResidue (n : ℕ) : residue (1 : ZMod 1) n = mertens n := by
  unfold residue mertens
  have he : range (n+1) = insert 0 (Icc 1 n) := by ext k;simp;omega
  have h (k : ℕ) : (k : ZMod 1) = 1 := Subsingleton.elim _ _
  simp_rw [if_pos (h _)]
  rw [he,sum_insert (by simp)]
  simp

private noncomputable def classes (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  univ.filter fun b => IsUnit b

private theorem mass {q : ℕ} [NeZero q] (n : ℕ) :
    ∑ b ∈ classes q, residue b n =
      ∑ k ∈ range (n+1), if IsUnit (k:ZMod q) then (ArithmeticFunction.moebius k:ℝ) else 0 := by
  classical
  unfold residue
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases hk : IsUnit (k:ZMod q)
  · rw [if_pos hk,sum_eq_single (k:ZMod q)]
    · simp
    · intro b _ hb
      exact if_neg (Ne.symm hb)
    · intro h
      exact (h (mem_filter.mpr ⟨mem_univ _,hk⟩)).elim
  · rw [if_neg hk]
    apply sum_eq_zero
    intro b hb
    apply if_neg
    intro e
    exact hk (e ▸ (mem_filter.mp hb).2)

theorem solution : centeredBound ↔ squareUpper := by
  constructor
  · intro H q _ a ha σ hhalf hone
    obtain ⟨C,hC,hs⟩ := (GRH.centered_moebius_bound_iff_square_mertens_residual q a σ hhalf.le).mp
      (H q a ha σ hhalf hone)
    refine ⟨C,hC,fun u => ?_⟩
    have h := (le_abs_self _).trans (hs u)
    have hpos : 0 ≤ (u:ℝ)^2*((1/(q:ℝ))*(GRH.reducedMoebiusHarmonic q u)^2) := by positivity
    change residue a (u^2) + _ ≤ _ at h
    linarith only [h,hpos]
  · intro H
    have hRH := GRH.riemannHypothesis_iff_upper_mertens_at_squares.mpr (by
      intro σ hhalf hone
      obtain ⟨C,hC,hs⟩ := H 1 1 isUnit_one σ hhalf hone
      exact ⟨C,hC,fun u => by rw [← ordinaryResidue];exact hs u⟩)
    intro q _ a ha σ hhalf hone
    classical
    obtain ⟨L,hL⟩ := moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hhalf
      (moebius_summatory_rpow_bound_of_riemannHypothesis hRH)
    let f := fun j : ℕ => (ArithmeticFunction.moebius j:ℝ)*(j:ℝ)^(-σ)
    obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hL.abs).bddAbove
    have hp (n : ℕ) : |∑ j ∈ range n, f j| ≤ max 0 B := by
      cases n with
      | zero => simp
      | succ n =>
        have he : range (n+1) = insert 0 (Icc 1 n) := by ext k;simp;omega
        rw [he,sum_insert (by simp),show f 0=0 by simp [f],zero_add]
        exact (hB ⟨n,rfl⟩).trans (le_max_right ..)
    obtain ⟨K,hK,_,htotal⟩ := GRH.reduced_moebius_principal_bounds_of_dirichlet_prefixes
      q σ (max 0 B) hhalf hone (le_max_left ..) hp
    have hall (b : ZMod q) : ∃ C : ℝ, 0 ≤ C ∧ (IsUnit b → ∀ u : ℕ,
        residue b (u^2) ≤ C*((u:ℝ)^2+1)^σ) := by
      by_cases hb : IsUnit b
      · obtain ⟨C,hC,Hb⟩ := H q b hb σ hhalf hone
        exact ⟨C,hC,fun _ => Hb⟩
      · exact ⟨0,le_rfl,fun h => (hb h).elim⟩
    choose C hC hclass using hall
    let D := ∑ b ∈ classes q, C b
    have hD : 0 ≤ D := sum_nonneg fun b _ => hC b
    have haS : a ∈ classes q := mem_filter.mpr ⟨mem_univ _,ha⟩
    apply (GRH.centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
      hRH q a ha σ hhalf hone).mpr
    right
    refine ⟨C a+D+6*K,add_nonneg (add_nonneg (hC a) hD) (mul_nonneg (by norm_num) hK),fun u => ?_⟩
    let X := ((u:ℝ)^2+1)^σ
    have hx : 0 ≤ X := Real.rpow_nonneg (by positivity) _
    let T := ∑ b ∈ classes q, residue b (u^2)
    have ht : |T| ≤ 3*K*X := by
      dsimp only [T]
      rw [mass]
      have h := htotal (u*u)
      rw [Nat.cast_mul] at h
      simpa only [X,pow_two] using h
    have hother : ∑ b ∈ (classes q).erase a, residue b (u^2) ≤ D*X := by
      calc
        _ ≤ ∑ b ∈ (classes q).erase a, C b*X := by
          apply sum_le_sum
          intro b hb
          exact hclass b (mem_filter.mp (mem_of_mem_erase hb)).2 u
        _ = (∑ b ∈ (classes q).erase a, C b)*X := (sum_mul ..).symm
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hx
          dsimp only [D]
          rw [← sum_erase_add (classes q) C haS]
          exact le_add_of_nonneg_right (hC a)
    have he : (∑ b ∈ (classes q).erase a, residue b (u^2)) + residue a (u^2) = T :=
      sum_erase_add _ _ haS
    have hraw : |residue a (u^2)| ≤ (C a + D + 3*K)*X := by
      apply abs_le.mpr
      constructor
      · nlinarith only [(abs_le.mp ht).1,hother,he,mul_nonneg (hC a) hx]
      · nlinarith only [hclass a ha u,mul_nonneg hD hx,mul_nonneg hK hx]
    have hφ : (1:ℝ) ≤ q.totient := by
      exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
    have hmean : |T/(q.totient:ℝ)| ≤ 3*K*X := by
      rw [abs_div,abs_of_nonneg (Nat.cast_nonneg q.totient : 0 ≤ (q.totient:ℝ))]
      exact (div_le_self (abs_nonneg _) hφ).trans ht
    rw [← mass]
    change |residue a (u^2)-T/(q.totient:ℝ)| ≤ (C a+D+6*K)*X
    exact (abs_sub _ _).trans ((add_le_add hraw hmean).trans_eq (by ring))
