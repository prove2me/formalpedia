-- Prove2me | solution 1 for ComputationalLearning.greedy_set_cover
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:24:29.465066+00:00
-- url     : https://prove2.me/submissions/41f94791-43ea-4eeb-97f1-40302ce11389

import Mathlib
import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory

namespace ComputationalLearning

theorem gsc_main {U : Type*} [DecidableEq U] [Fintype U] (𝒮 : Finset (Finset U))
    (hcov : IsCover 𝒮 𝒮) (t : ℕ → Finset U) (ht : IsGreedySequence 𝒮 t) :
    (∀ i : ℕ, ((uncovered t i).card : ℝ) ≤
      (1 - 1 / (optCover 𝒮 : ℝ)) ^ i * (Fintype.card U : ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → (optCover 𝒮 : ℝ) * Real.log (Fintype.card U) ≤ i →
      uncovered t i = ∅) := by
  classical
  set k := optCover 𝒮 with hk
  have hne : {k | ∃ T, IsCover 𝒮 T ∧ T.card = k}.Nonempty := ⟨𝒮.card, 𝒮, hcov, rfl⟩
  obtain ⟨T, hT, hTcard⟩ : ∃ T, IsCover 𝒮 T ∧ T.card = k := Nat.sInf_mem hne
  have hstep_sub : ∀ i, uncovered t (i + 1) = uncovered t i \ t i := by
    intro i; ext u
    simp only [uncovered, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro h; exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h1 j hj
      · exact h2
  have hcard_step : ∀ i, ((uncovered t (i + 1)).card : ℝ) ≤
      (1 - 1 / (k : ℝ)) * (uncovered t i).card := by
    intro i
    have e1 : (uncovered t (i + 1)).card + (uncovered t i ∩ t i).card =
        (uncovered t i).card := by
      rw [hstep_sub]; exact Finset.card_sdiff_add_card_inter _ _
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0]
      have : (uncovered t (i + 1)).card ≤ (uncovered t i).card := by omega
      simp only [CharP.cast_eq_zero, div_zero, sub_zero, one_mul]
      exact_mod_cast this
    · have hcovU : (uncovered t i).card ≤ k * (t i ∩ uncovered t i).card := by
        calc (uncovered t i).card ≤ (T.biUnion (fun s => s ∩ uncovered t i)).card := by
              apply Finset.card_le_card
              intro u hu
              obtain ⟨s, hsT, hus⟩ := hT.2 u
              exact Finset.mem_biUnion.mpr ⟨s, hsT, Finset.mem_inter.mpr ⟨hus, hu⟩⟩
          _ ≤ ∑ s ∈ T, (s ∩ uncovered t i).card := Finset.card_biUnion_le
          _ ≤ ∑ s ∈ T, (t i ∩ uncovered t i).card :=
              Finset.sum_le_sum fun s hs => (ht i).2 s (hT.1 hs)
          _ = k * (t i ∩ uncovered t i).card := by rw [Finset.sum_const, hTcard, smul_eq_mul]
      have hinter : (uncovered t i ∩ t i).card = (t i ∩ uncovered t i).card := by
        rw [Finset.inter_comm]
      have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
      have e1R : ((uncovered t (i + 1)).card : ℝ) =
          (uncovered t i).card - (t i ∩ uncovered t i).card := by
        rw [hinter] at e1
        have e1' : ((uncovered t (i + 1)).card : ℝ) + (t i ∩ uncovered t i).card =
            (uncovered t i).card := by exact_mod_cast e1
        linarith
      have hcovR : ((uncovered t i).card : ℝ) ≤ k * (t i ∩ uncovered t i).card := by
        exact_mod_cast hcovU
      rw [e1R]
      have h2 : ((uncovered t i).card : ℝ) / k ≤ (t i ∩ uncovered t i).card := by
        rw [div_le_iff₀ hkR]; linarith
      calc ((uncovered t i).card : ℝ) - (t i ∩ uncovered t i).card ≤
          (uncovered t i).card - (uncovered t i).card / k := by linarith
        _ = (1 - 1 / (k:ℝ)) * (uncovered t i).card := by ring
  have hfac : 0 ≤ 1 - 1 / (k : ℝ) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0]; simp
    · have h1 : (1:ℝ) ≤ k := by exact_mod_cast hkpos
      have : 1 / (k:ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
      linarith
  have part1 : ∀ i : ℕ, ((uncovered t i).card : ℝ) ≤
      (1 - 1 / (k : ℝ)) ^ i * (Fintype.card U : ℝ) := by
    intro i
    induction i with
    | zero =>
      simp only [pow_zero, one_mul]
      exact_mod_cast Finset.card_le_univ _
    | succ i ih =>
      calc ((uncovered t (i + 1)).card : ℝ) ≤ (1 - 1 / (k : ℝ)) * (uncovered t i).card :=
            hcard_step i
        _ ≤ (1 - 1 / (k : ℝ)) * ((1 - 1 / (k : ℝ)) ^ i * (Fintype.card U : ℝ)) :=
            mul_le_mul_of_nonneg_left ih hfac
        _ = (1 - 1 / (k : ℝ)) ^ (i + 1) * (Fintype.card U : ℝ) := by ring
  refine ⟨part1, fun i hi hlog => ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card U) with hU0 | hUpos
  · haveI : IsEmpty U := Fintype.card_eq_zero_iff.mp hU0
    exact Finset.eq_empty_of_forall_notMem (fun u _ => IsEmpty.false u)
  · have hkpos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      obtain ⟨u⟩ : Nonempty U := Fintype.card_pos_iff.mp hUpos
      obtain ⟨s, hsT, _⟩ := hT.2 u
      have hT0 : T.card = 0 := by rw [hTcard, hk0]
      rw [Finset.card_eq_zero] at hT0
      rw [hT0] at hsT
      exact Finset.notMem_empty _ hsT
    have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
    have hUR : (0:ℝ) < Fintype.card U := by exact_mod_cast hUpos
    have hlt : ((uncovered t i).card : ℝ) < 1 := by
      calc ((uncovered t i).card : ℝ) ≤ (1 - 1 / (k : ℝ)) ^ i * (Fintype.card U : ℝ) := part1 i
        _ < (Real.exp (-(1 / (k:ℝ)))) ^ i * (Fintype.card U : ℝ) := by
            apply mul_lt_mul_of_pos_right _ hUR
            apply pow_lt_pow_left₀ _ hfac (by omega)
            have hpos : 0 < 1 / (k:ℝ) := by positivity
            have := Real.add_one_lt_exp (show -(1 / (k:ℝ)) ≠ 0 by linarith)
            linarith
        _ = Real.exp (-(i / (k:ℝ))) * (Fintype.card U : ℝ) := by
            rw [← Real.exp_nat_mul]; congr 2; ring
        _ ≤ Real.exp (-Real.log (Fintype.card U)) * (Fintype.card U : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hUR.le
            apply Real.exp_le_exp.mpr
            have : Real.log (Fintype.card U) ≤ i / (k:ℝ) := by
              rw [le_div_iff₀ hkR]; linarith
            linarith
        _ = 1 := by rw [Real.exp_neg, Real.exp_log hUR]; field_simp
    have hlt' : (uncovered t i).card < 1 := by exact_mod_cast hlt
    exact Finset.card_eq_zero.mp (by omega)

end ComputationalLearning

open ComputationalLearning

theorem solution {U : Type*} [DecidableEq U] [Fintype U] (𝒮 : Finset (Finset U))
    (hcov : IsCover 𝒮 𝒮) (t : ℕ → Finset U) (ht : IsGreedySequence 𝒮 t) :
    (∀ i : ℕ, ((uncovered t i).card : ℝ) ≤
      (1 - 1 / (optCover 𝒮 : ℝ)) ^ i * (Fintype.card U : ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → (optCover 𝒮 : ℝ) * Real.log (Fintype.card U) ≤ i →
      uncovered t i = ∅) := by
  exact gsc_main 𝒮 hcov t ht
