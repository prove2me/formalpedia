-- Prove2me | solution 1 for CommitteeVoting.SingleVoter.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:28:32.427777+00:00
-- url     : https://prove2.me/submissions/79ad9c2b-3ace-424a-a01a-16fa61cc1716

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial
set_option autoImplicit false
open CommitteeVoting.SingleVoter

section
variable {ι : Type*} [DecidableEq ι]

theorem pbWeight_nonneg (q : ι → ℝ) (S A : Finset ι) (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ 1)
    (hA : A ⊆ S) : 0 ≤ pbWeight q S A := by
  unfold pbWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i hi => (hq i (hA hi)).1)
  · exact Finset.prod_nonneg (fun i hi => by have := (hq i (Finset.mem_sdiff.mp hi).1).2; linarith)

theorem pbPMF_nonneg (q : ι → ℝ) (S : Finset ι) (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ 1) (ℓ : ℕ) :
    0 ≤ pbPMF q S ℓ := by
  unfold pbPMF
  apply Finset.sum_nonneg
  intro A hA
  exact pbWeight_nonneg q S A hq (Finset.mem_powersetCard.mp hA).1

theorem pbPMF_insert_zero (q : ι → ℝ) (S : Finset ι) (a : ι) (ha : a ∉ S) :
    pbPMF q (insert a S) 0 = (1 - q a) * pbPMF q S 0 := by
  unfold pbPMF pbWeight
  simp [Finset.prod_insert ha]

theorem pbPMF_insert_succ (q : ι → ℝ) (S : Finset ι) (a : ι) (ha : a ∉ S) (ℓ : ℕ) :
    pbPMF q (insert a S) (ℓ + 1) = q a * pbPMF q S ℓ + (1 - q a) * pbPMF q S (ℓ + 1) := by
  unfold pbPMF
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [Finset.mul_sum, Finset.mul_sum, add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro A hA
        have hAS := (Finset.mem_powersetCard.mp hA).1
        have haA : a ∉ A := fun h => ha (hAS h)
        unfold pbWeight
        have : insert a S \ insert a A = S \ A := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact absurd (Or.inl h1) h2
            · exact ⟨h1, fun h => h2 (Or.inr h)⟩
          · rintro ⟨h1, h2⟩
            refine ⟨Or.inr h1, ?_⟩
            rintro (h | h)
            · subst h; exact ha h1
            · exact h2 h
        rw [this, Finset.prod_insert haA]
        ring
      · apply Finset.sum_congr rfl
        intro A hA
        have hAS := (Finset.mem_powersetCard.mp hA).1
        have haA : a ∉ A := fun h => ha (hAS h)
        unfold pbWeight
        have : insert a S \ A = insert a (S \ A) := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact Or.inl h1
            · exact Or.inr ⟨h1, h2⟩
          · rintro (h | ⟨h1, h2⟩)
            · subst h; exact ⟨Or.inl rfl, haA⟩
            · exact ⟨Or.inr h1, h2⟩
        rw [this, Finset.prod_insert (fun h => ha (Finset.mem_sdiff.mp h).1)]
        ring
    · intro A hA B hB hAB
      have hA' := (Finset.mem_powersetCard.mp hA).1
      have hB' := (Finset.mem_powersetCard.mp hB).1
      have haA : a ∉ A := fun h => ha (hA' h)
      have haB : a ∉ B := fun h => ha (hB' h)
      have := congrArg (fun X => Finset.erase X a) hAB
      simpa [Finset.erase_insert haA, Finset.erase_insert haB] using this
  · rw [Finset.disjoint_left]
    intro A hA hA2
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hA2
    have := (Finset.mem_powersetCard.mp hA).1 (Finset.mem_insert_self a B)
    exact ha this

theorem pbCDF_insert_zero (q : ι → ℝ) (S : Finset ι) (a : ι) (ha : a ∉ S) :
    pbCDF q (insert a S) 0 = (1 - q a) * pbCDF q S 0 := by
  unfold pbCDF
  simp [pbPMF_insert_zero q S a ha]

theorem pbCDF_insert_succ (q : ι → ℝ) (S : Finset ι) (a : ι) (ha : a ∉ S) (x : ℕ) :
    pbCDF q (insert a S) (x + 1) = (1 - q a) * pbCDF q S (x + 1) + q a * pbCDF q S x := by
  induction x with
  | zero =>
    unfold pbCDF
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [pbPMF_insert_zero q S a ha, pbPMF_insert_succ q S a ha]
    ring
  | succ x ih =>
    have h1 : pbCDF q (insert a S) (x + 1 + 1) = pbCDF q (insert a S) (x + 1) + pbPMF q (insert a S) (x + 1 + 1) := by
      unfold pbCDF; rw [Finset.sum_range_succ _ (x + 1 + 1)]
    have h2 : pbCDF q S (x + 1 + 1) = pbCDF q S (x + 1) + pbPMF q S (x + 1 + 1) := by
      unfold pbCDF; rw [Finset.sum_range_succ _ (x + 1 + 1)]
    have h3 : pbCDF q S (x + 1) = pbCDF q S x + pbPMF q S (x + 1) := by
      unfold pbCDF; rw [Finset.sum_range_succ _ (x + 1)]
    rw [h1, ih, pbPMF_insert_succ q S a ha, h2, h3]
    ring

theorem pbCDF_mono_x (q : ι → ℝ) (S : Finset ι) (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ 1) (x : ℕ) :
    pbCDF q S x ≤ pbCDF q S (x + 1) := by
  unfold pbCDF
  rw [Finset.sum_range_succ _ (x + 1)]
  have := pbPMF_nonneg q S hq (x + 1)
  linarith

theorem pbCDF_nonneg (q : ι → ℝ) (S : Finset ι) (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ 1) (x : ℕ) :
    0 ≤ pbCDF q S x := by
  unfold pbCDF
  exact Finset.sum_nonneg (fun l _ => pbPMF_nonneg q S hq l)

theorem pbCDF_anti (q q' : ι → ℝ) (S : Finset ι) (hq : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ q' i ∧ q' i ≤ 1) :
    ∀ x : ℕ, pbCDF q' S x ≤ pbCDF q S x := by
  induction S using Finset.induction_on with
  | empty =>
    intro x
    unfold pbCDF
    apply le_of_eq; apply Finset.sum_congr rfl
    intro l _
    rcases l with _ | l
    · simp [pbPMF, pbWeight]
    · simp [pbPMF, pbWeight, Finset.powersetCard_eq_empty.mpr (show (∅ : Finset ι).card < l + 1 by simp)]
  | insert a S ha ih =>
    intro x
    have hqS : ∀ i ∈ S, 0 ≤ q i ∧ q i ≤ q' i ∧ q' i ≤ 1 := fun i hi => hq i (Finset.mem_insert_of_mem hi)
    have hq'S : ∀ i ∈ S, 0 ≤ q' i ∧ q' i ≤ 1 := fun i hi =>
      ⟨le_trans (hqS i hi).1 (hqS i hi).2.1, (hqS i hi).2.2⟩
    obtain ⟨h0, h1, h2⟩ := hq a (Finset.mem_insert_self a S)
    cases x with
    | zero =>
      rw [pbCDF_insert_zero _ _ _ ha, pbCDF_insert_zero _ _ _ ha]
      have := ih hqS 0
      have hn := pbCDF_nonneg q' S hq'S 0
      nlinarith
    | succ x =>
      rw [pbCDF_insert_succ _ _ _ ha, pbCDF_insert_succ _ _ _ ha]
      have e1 := ih hqS (x + 1)
      have e2 := ih hqS x
      have e3 := pbCDF_mono_x q' S hq'S x
      nlinarith

end

theorem solution {n : ℕ} (p p' : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hpp' : ∀ i, p i ≤ p' i)
    (hp'1 : ∀ i, p' i ≤ 1) (x : ℕ) :
    pbCDF p' Finset.univ x ≤ pbCDF p Finset.univ x :=
  pbCDF_anti p p' Finset.univ (fun i _ => ⟨hp0 i, hpp' i, hp'1 i⟩) x
