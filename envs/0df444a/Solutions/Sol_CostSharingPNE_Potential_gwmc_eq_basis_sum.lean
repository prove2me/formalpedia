-- Prove2me | solution 1 for CostSharingPNE.Potential.gwmc_eq_basis_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:04:02.179947+00:00
-- url     : https://prove2.me/submissions/04ca0b4a-b6eb-4eac-9f33-8566fe559b3a

import Mathlib
import Definitions.Def_CostSharingPNE_Potential_Setting

set_option autoImplicit false
open CostSharingPNE.Potential CostSharingPNE.Char

lemma CSP_mobius_insert {n : ℕ} (W : Welfare n) (a : Fin n) (T : Finset (Fin n)) (ha : a ∉ T) :
    mobius W (insert a T) = mobius (fun R => W (insert a R)) T - mobius W T := by
  unfold mobius
  have e1 : ∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card + 1 - R.card) * W R =
      -∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card - R.card) * W R := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro R hR
    have := Finset.card_le_card (Finset.mem_powerset.1 hR)
    rw [show T.card + 1 - R.card = (T.card - R.card) + 1 by omega, pow_succ]
    ring
  have e2 : ∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card + 1 - (insert a R).card) * W (insert a R) =
      ∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card - R.card) * W (insert a R) := by
    apply Finset.sum_congr rfl
    intro R hR
    have haR : a ∉ R := fun h => ha (Finset.mem_powerset.1 hR h)
    rw [Finset.card_insert_of_notMem haR]
    congr 2
    omega
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha, e1, e2]
  ring

lemma CSP_mobius_sum {n : ℕ} : ∀ (U : Finset (Fin n)) (W : Welfare n),
    ∑ T ∈ U.powerset, mobius W T = W U := by
  intro U
  induction U using Finset.induction_on with
  | empty => intro W; simp [mobius]
  | insert a U ha ih =>
    intro W
    rw [Finset.sum_powerset_insert ha]
    have h : ∀ T ∈ U.powerset, mobius W (insert a T) =
        mobius (fun R => W (insert a R)) T - mobius W T :=
      fun T hT => CSP_mobius_insert W a T (fun h => ha (Finset.mem_powerset.1 hT h))
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ih W, ih (fun R => W (insert a R))]
    ring

theorem solution {n : ℕ} (ω : CostSharingPNE.Char.WeightSystem n) (W : CostSharingPNE.Char.Welfare n) :
    ∀ S : Finset (Fin n), ∀ i ∈ S,
      CostSharingPNE.Char.gwmc ω W i S =
        ∑ T ∈ S.powerset.filter Finset.Nonempty,
          CostSharingPNE.Char.mobius W T * gwmcBasis ω T i S := by
  intro S i hi
  set U := sbar ω S (ω.block i) with hU
  have hiU : i ∈ U := by simp [hU, sbar, hi]
  have hset : (S.powerset.filter Finset.Nonempty).filter (fun T => i ∈ tbar ω T ∧ T ⊆ S) =
      U.powerset.filter (fun T => i ∈ T) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨_, hne⟩, hit, hTS⟩
      simp only [tbar, dif_pos hne, Finset.mem_filter] at hit
      obtain ⟨hiT, hbi⟩ := hit
      refine ⟨?_, hiT⟩
      intro j hj
      simp only [hU, sbar, Finset.mem_filter]
      refine ⟨hTS hj, ?_⟩
      rw [hbi]
      exact Finset.inf'_le _ hj
    · rintro ⟨hTU, hiT⟩
      have hTS : T ⊆ S := fun j hj => (Finset.mem_filter.1 (hTU hj)).1
      have hne : T.Nonempty := ⟨i, hiT⟩
      refine ⟨⟨hTS, hne⟩, ?_, hTS⟩
      simp only [tbar, dif_pos hne, Finset.mem_filter]
      refine ⟨hiT, le_antisymm ?_ (Finset.inf'_le _ hiT)⟩
      apply Finset.le_inf'
      intro j hj
      exact (Finset.mem_filter.1 (hTU hj)).2
  have hsplit : ∑ T ∈ U.powerset.filter (fun T => i ∈ T), mobius W T =
      W U - W (U.erase i) := by
    have h1 := Finset.sum_filter_add_sum_filter_not U.powerset (fun T => i ∈ T) (mobius W)
    have h2 : U.powerset.filter (fun T => ¬ i ∈ T) = (U.erase i).powerset := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        exact Finset.mem_erase.2 ⟨fun h => h2 (h ▸ hj), h1 hj⟩
      · intro h
        exact ⟨fun j hj => (Finset.mem_erase.1 (h hj)).2, fun hi => (Finset.mem_erase.1 (h hi)).1 rfl⟩
    rw [h2, CSP_mobius_sum, CSP_mobius_sum] at h1
    linarith
  simp only [gwmcBasis, mul_ite, mul_zero]
  rw [← Finset.sum_filter, hset, ← Finset.sum_mul, hsplit]
  unfold gwmc
  rw [if_pos hi]
  ring
