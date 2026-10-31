-- Prove2me | solution 1 for FramingFulfillment.RFF.framing_decomposition_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:04:03.285979+00:00
-- url     : https://prove2.me/submissions/bf3f96f8-c584-4615-8dd3-7bf7a22196ae

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

open FramingFulfillment.RFF Finset

theorem solution {N R : ℕ} (Qt : Fin R → ℕ) (B : Fin N → Fin R → ℝ)
    (hB : ∀ n r, 0 ≤ B n r) (hF : IsFramingMatrix B Qt) :
    ∃ (L : ℕ) (α : Fin L → ℝ) (Bs : Fin L → Fin N → Fin R → ℝ),
      IsFramingDecomposition B Qt α Bs := by
  classical
  obtain ⟨hrow, hcol⟩ := hF
  -- slots
  let S := (r : Fin R) × Fin (Qt r)
  have hcard : Fintype.card S = N := by
    have h1 : (∑ n : Fin N, ∑ r, B n r) = (N : ℝ) := by simp [hrow]
    have h2 : (∑ n : Fin N, ∑ r, B n r) = ((∑ r, Qt r : ℕ) : ℝ) := by
      rw [Finset.sum_comm]; push_cast; simp [hcol]
    have : (∑ r, Qt r : ℕ) = N := by exact_mod_cast h2.symm.trans h1
    simp [S, Fintype.card_sigma, this]
  let e : Fin N ≃ S := (Fintype.equivOfCardEq (by simp [hcard])).symm
  -- B n r = 0 when Qt r = 0
  have hz : ∀ n r, Qt r = 0 → B n r = 0 := by
    intro n r hr
    have h := hcol r
    rw [hr] at h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hB i r)).1 (by simpa using h) n
    exact this (Finset.mem_univ _)
  -- key: summing over slots of a column
  have hslot : ∀ (g : Fin R → ℝ) (r : Fin R),
      (∑ m : Fin N, if (e m).1 = r then g (e m).1 else 0) = (Qt r : ℝ) * g r := by
    intro g r
    rw [Equiv.sum_comp e (fun s => if s.1 = r then g s.1 else 0)]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single r]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  let D : Matrix (Fin N) (Fin N) ℝ := fun n m => B n (e m).1 / (Qt (e m).1 : ℝ)
  have hD : D ∈ doublyStochastic ℝ (Fin N) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun n m => div_nonneg (hB _ _) (Nat.cast_nonneg _), ?_, ?_⟩
    · intro n
      have : ∀ m, D n m = ∑ r, if (e m).1 = r then B n (e m).1 / (Qt (e m).1 : ℝ) else 0 := by
        intro m; simp [D]
      simp_rw [this]
      rw [Finset.sum_comm]
      simp_rw [hslot (fun r => B n r / (Qt r : ℝ))]
      rw [← hrow n]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hq : Qt r = 0
      · simp [hq, hz n r hq]
      · field_simp
    · intro m
      simp only [D]
      rw [← Finset.sum_div, hcol]
      have : Qt (e m).1 ≠ 0 := by
        have := (e m).2.pos; omega
      field_simp
  obtain ⟨w, hw0, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  let A : Equiv.Perm (Fin N) → Fin N → Fin R → ℝ :=
    fun σ n r => if (e (σ n)).1 = r then 1 else 0
  have hDent : ∀ n m, D n m = ∑ σ, w σ * (if σ n = m then 1 else 0) := by
    intro n m
    rw [← hwD]
    simp [Matrix.sum_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hBrep : ∀ n r, B n r = ∑ σ, w σ * A σ n r := by
    intro n r
    have h1 : ∀ σ : Equiv.Perm (Fin N), A σ n r =
        ∑ m : Fin N, (if σ n = m then 1 else 0) * (if (e m).1 = r then 1 else 0) := by
      intro σ
      rw [Finset.sum_eq_single (σ n)]
      · simp [A]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ m : Fin N, (∑ σ : Equiv.Perm (Fin N),
        w σ * ((if σ n = m then 1 else 0) * (if (e m).1 = r then 1 else 0))) =
        if (e m).1 = r then B n (e m).1 / (Qt (e m).1 : ℝ) else 0 := by
      intro m
      have := hDent n m
      simp only [D] at this
      split_ifs with h
      · rw [this]; simp
      · simp
    simp_rw [h2]
    rw [hslot (fun r => B n r / (Qt r : ℝ)) r]
    by_cases hq : Qt r = 0
    · simp [hq, hz n r hq]
    · field_simp
  have hAint : ∀ σ, IsIntegralMatrix (A σ) := by
    intro σ n r; simp only [A]; split_ifs <;> simp
  have hAfr : ∀ σ, IsFramingMatrix (A σ) Qt := by
    intro σ
    refine ⟨fun n => ?_, fun r => ?_⟩
    · simp [A]
    · have := hslot (fun _ => (1 : ℝ)) r
      simp only [mul_one] at this
      rw [← this]
      simp only [A]
      exact Equiv.sum_comp σ (fun m => if (e m).1 = r then (1:ℝ) else 0)
  -- index positive weights
  let s := (univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => 0 < w σ)
  let f := s.equivFin
  have hsum : ∀ g : Equiv.Perm (Fin N) → ℝ, (∀ σ, w σ = 0 → g σ = 0) →
      (∑ l : Fin s.card, g (f.symm l)) = ∑ σ, g σ := by
    intro g hg
    rw [Equiv.sum_comp f.symm (fun x : s => g x)]
    rw [Finset.sum_coe_sort s g]
    rw [Finset.sum_filter_of_ne]
    intro σ _ hσ
    rcases (hw0 σ).lt_or_eq with h | h
    · exact h
    · exact absurd (hg σ h.symm) hσ
  refine ⟨s.card, fun l => w (f.symm l), fun l => A (f.symm l), ?_, ?_, ?_, ?_⟩
  · intro l
    have hpos : 0 < w (f.symm l) := (Finset.mem_filter.1 (f.symm l).2).2
    refine ⟨hpos, ?_⟩
    rw [← hw1]
    exact Finset.single_le_sum (fun σ _ => hw0 σ) (Finset.mem_univ _)
  · rw [hsum w (fun σ h => h), hw1]
  · intro l; exact ⟨hAint _, hAfr _⟩
  · intro n r
    rw [hBrep n r]
    exact (hsum (fun σ => w σ * A σ n r) (fun σ h => by simp [h])).symm
