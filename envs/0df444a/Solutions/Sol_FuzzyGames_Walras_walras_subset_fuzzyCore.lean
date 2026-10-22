-- Prove2me | solution 1 for FuzzyGames.Walras.walras_subset_fuzzyCore
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:11:23.664838+00:00
-- url     : https://prove2.me/submissions/75449811-0ae6-4a6a-8b97-4ee299b24aea

import Mathlib
import Definitions.Def_FuzzyGames_Walras_Basic



namespace FuzzyGames.Walras

open Set Pointwise

variable {n l : ℕ}

lemma dot_add' (p y z : Fin l → ℝ) : dot p (y + z) = dot p y + dot p z := by
  unfold dot; simp [mul_add, Finset.sum_add_distrib]

lemma dot_smul' (p : Fin l → ℝ) (a : ℝ) (y : Fin l → ℝ) : dot p (a • y) = a * dot p y := by
  unfold dot; simp [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma dot_sub' (p y z : Fin l → ℝ) : dot p (y - z) = dot p y - dot p z := by
  unfold dot; simp [mul_sub, Finset.sum_sub_distrib]

lemma dot_zero' (p : Fin l → ℝ) : dot p 0 = 0 := by simp [dot]

lemma dot_sum' (p : Fin l → ℝ) {ι : Type*} (s : Finset ι) (f : ι → Fin l → ℝ) :
    dot p (∑ i ∈ s, f i) = ∑ i ∈ s, dot p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dot_add', ih]

lemma mem_Ytau {E : Economy n l} {τ : Fin n → ℝ} {s : Fin l → ℝ} (h : s ∈ E.Ytau τ) :
    ∃ y : Fin n → Fin l → ℝ, (∀ i, y i ∈ E.Y i) ∧ s = ∑ i, τ i • y i := by
  unfold Economy.Ytau at h
  rw [Set.mem_finset_sum] at h
  obtain ⟨g, hg, hs⟩ := h
  have : ∀ i, ∃ y, y ∈ E.Y i ∧ τ i • y = g i := fun i => by
    obtain ⟨y, hy, e⟩ := hg (Finset.mem_univ i); exact ⟨y, hy, e⟩
  choose y hy he using this
  exact ⟨y, hy, by rw [← hs]; exact Finset.sum_congr rfl (fun i _ => (he i).symm)⟩

lemma mem_Ytau_of {E : Economy n l} {τ : Fin n → ℝ} (y : Fin n → Fin l → ℝ) (hy : ∀ i, y i ∈ E.Y i) :
    ∑ i, τ i • y i ∈ E.Ytau τ := by
  unfold Economy.Ytau
  rw [Set.mem_finset_sum]
  exact ⟨fun i => τ i • y i, fun {i} _ => Set.smul_mem_smul_set (hy i), rfl⟩

theorem walras_sub_core (E : Economy n l) (hE : E.Assumptions) : E.walras ⊆ E.fuzzyCore := by
  rintro x ⟨hx1, p, hinc, hopt⟩
  refine ⟨hx1, ?_⟩
  rintro τ hτ hτ0 ⟨xt, ⟨hxt0, hxtY⟩, hxt⟩
  have hc : ∀ i, ∀ y ∈ E.Y i, dot p y ≤ dot p (x i) := by
    intro i y hy
    have : ((dot p y : ℝ) : EReal) ≤ E.income i p :=
      le_iSup₂ (f := fun y (_ : y ∈ E.Y i) => ((dot p y : ℝ) : EReal)) y hy
    rw [← hinc i] at this
    exact_mod_cast this
  have hs : ∀ i, 0 < τ i → dot p (x i) < dot p (xt i) := by
    intro i hi
    by_contra hle
    push_neg at hle
    have hbud : xt i ∈ E.budget i p := ⟨hxt0 i hi, by rw [← hinc i]; exact_mod_cast hle⟩
    exact (hxt i hi).2 (hopt i _ hbud)
  obtain ⟨y, hy, hsum⟩ := mem_Ytau hxtY
  have hτ0' : ∀ i, 0 ≤ τ i := fun i => hτ.1 i
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < τ i := by
    by_contra hcon
    push_neg at hcon
    apply hτ0
    funext i
    exact le_antisymm (hcon i) (hτ0' i)
  have h1 : dot p (∑ i, τ i • xt i) = ∑ i, τ i * dot p (xt i) := by
    rw [dot_sum']; exact Finset.sum_congr rfl (fun i _ => dot_smul' _ _ _)
  have h2 : dot p (∑ i, τ i • y i) = ∑ i, τ i * dot p (y i) := by
    rw [dot_sum']; exact Finset.sum_congr rfl (fun i _ => dot_smul' _ _ _)
  have h3 : ∑ i, τ i * dot p (x i) < ∑ i, τ i * dot p (xt i) := by
    apply Finset.sum_lt_sum
    · intro i _
      rcases (hτ0' i).eq_or_lt with h | h
      · rw [← h]; simp
      · exact le_of_lt (mul_lt_mul_of_pos_left (hs i h) h)
    · exact ⟨i0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hs i0 hi0) hi0⟩
  have h4 : ∑ i, τ i * dot p (y i) ≤ ∑ i, τ i * dot p (x i) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i _ (hy i)) (hτ0' i))
  have : ∑ i, τ i * dot p (xt i) = ∑ i, τ i * dot p (y i) := by
    rw [← h1, ← h2, hsum]
  linarith

end FuzzyGames.Walras

open FuzzyGames.Walras


theorem solution {n l : ℕ} (E : Economy n l) (hE : E.Assumptions) :
    E.walras ⊆ E.fuzzyCore := by
  exact walras_sub_core E hE
