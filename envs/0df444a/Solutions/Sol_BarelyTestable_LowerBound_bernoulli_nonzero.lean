-- Prove2me | solution 1 for BarelyTestable.LowerBound.bernoulli_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:59:28.942422+00:00
-- url     : https://prove2.me/submissions/4312d8f2-fc4e-4da4-ac02-a7cf45c94afe

import Definitions.Def_BarelyTestable_LowerBound_Cube

noncomputable section
open BarelyTestable.LowerBound NonmonotoneSubmod.Shared
namespace Submod722.BernoulliProof
variable {α : Type} [Fintype α] [DecidableEq α]

 def weight (q : α → ℝ) (R S : Finset α) : ℝ :=
  ∏ i ∈ R, if i ∈ S then q i else 1 - q i

 def prob (q : α → ℝ) (R : Finset α) (P : Finset α → Prop) : ℝ := by
  classical
  exact ∑ S ∈ R.powerset, if P S then weight q R S else 0

lemma weight_insert_absent (q : α → ℝ) (R S : Finset α) (a : α)
    (ha : a ∉ R) (has : a ∉ S) :
    weight q (insert a R) S = (1-q a)*weight q R S := by
  simp [weight, Finset.prod_insert ha, has]

lemma weight_insert_present (q : α → ℝ) (R S : Finset α) (a : α)
    (ha : a ∉ R) :
    weight q (insert a R) (insert a S) = q a*weight q R S := by
  rw [weight, Finset.prod_insert ha]
  simp only [Finset.mem_insert_self, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hia : i ≠ a := by rintro rfl; exact ha hi
  simp [hia]

lemma prob_insert (q : α → ℝ) (R : Finset α) (a : α) (ha : a ∉ R)
    (P : Finset α → Prop) :
    prob q (insert a R) P = (1-q a)*prob q R P + q a*prob q R (fun S => P (insert a S)) := by
  classical
  unfold prob
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    have has : a ∉ S := fun h => ha ((Finset.mem_powerset.mp hS) h)
    rw [weight_insert_absent q R S a ha has]
    split <;> simp_all
  · apply Finset.sum_congr rfl
    intro S hS
    rw [weight_insert_present q R S a ha]
    split <;> simp_all

lemma prob_true (q : α → ℝ) (R : Finset α) : prob q R (fun _ => True) = 1 := by
  induction R using Finset.induction_on with
  | empty => simp [prob, weight]
  | @insert a R ha ih => rw [prob_insert q R a ha, ih]; ring

lemma weight_nonneg (q : α → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (R S : Finset α) : 0 ≤ weight q R S := by
  apply Finset.prod_nonneg
  intro i hi
  split
  · exact (hq i).1
  · exact sub_nonneg.mpr (hq i).2

lemma submodular_insert (f : Oracle α) (hf : Submodular f) (a : α) :
    Submodular (fun S => f (insert a S)) := by
  intro S T
  have hU : insert a S ∪ insert a T = insert a (S ∪ T) := by ext; simp <;> tauto
  have hI : insert a S ∩ insert a T = insert a (S ∩ T) := by ext; simp <;> tauto
  simpa only [hU,hI] using hf (insert a S) (insert a T)

lemma nonzero_bound (q : α → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (c : ℝ) (hc1 : c ≤ 1) (hcq : ∀ i, c ≤ q i ∧ c ≤ 1-q i)
    (R : Finset α) (f : Oracle α) (hf : Submodular f) (h0 : 0 < f ∅) :
    c ≤ prob q R (fun S => f S ≠ 0) := by
  classical
  induction R using Finset.induction_on generalizing f with
  | empty => simpa [prob, weight, ne_of_gt h0] using hc1
  | @insert a R ha ih =>
    by_cases hfap : 0 < f {a}
    · have h1 := ih f hf h0
      have h2 := ih (fun S => f (insert a S)) (submodular_insert f hf a) (by simpa using hfap)
      rw [prob_insert q R a ha]
      nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr (hq a).2),
        mul_le_mul_of_nonneg_left h2 (hq a).1]
    · rw [prob_insert q R a ha]
      rw [prob, prob, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      have ht : c = ∑ S ∈ R.powerset, c*weight q R S := by
        rw [← Finset.mul_sum]
        have hnorm := prob_true q R
        simp only [prob, if_true] at hnorm
        rw [hnorm, mul_one]
      rw [ht]
      apply Finset.sum_le_sum
      intro S hS
      have hw := weight_nonneg q hq R S
      have has : a ∉ S := fun h => ha ((Finset.mem_powerset.mp hS) h)
      have hboth : f S ≠ 0 ∨ f (insert a S) ≠ 0 := by
        by_cases hfS : f S = 0
        · right
          have hU : S ∪ {a} = insert a S := by ext; simp <;> tauto
          have hI : S ∩ {a} = ∅ := by ext; simp; grind
          have hh := hf S {a}
          rw [hU,hI,hfS] at hh
          exact ne_of_lt (by linarith)
        · exact Or.inl hfS
      rcases hboth with hleft | hright
      · by_cases hh : f (insert a S) ≠ 0
        · simp only [if_pos hleft, if_pos hh]
          nlinarith [mul_le_mul_of_nonneg_right hc1 hw]
        · simp only [if_pos hleft, if_neg hh, mul_zero, add_zero]
          exact mul_le_mul_of_nonneg_right (hcq a).2 hw
      · by_cases hh : f S ≠ 0
        · simp only [if_pos hh, if_pos hright]
          nlinarith [mul_le_mul_of_nonneg_right hc1 hw]
        · simp only [if_neg hh, if_pos hright, mul_zero, zero_add]
          exact mul_le_mul_of_nonneg_right (hcq a).1 hw

lemma fold_min_le_init (l : List ℝ) (a : ℝ) : l.foldl min a ≤ a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons b l ih => exact (ih (min a b)).trans (min_le_left _ _)

lemma fold_min_le_mem (l : List ℝ) (a b : ℝ) (hb : b ∈ l) : l.foldl min a ≤ b := by
  induction l generalizing a with
  | nil => simp at hb
  | cons x l ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (fold_min_le_init l (min a b)).trans (min_le_right _ _)
    · exact ih (min a x) hb

lemma minBias_le {n : ℕ} (q : Fin n → ℝ) :
    minBias q ≤ 1 ∧ ∀ i, minBias q ≤ q i ∧ minBias q ≤ 1-q i := by
  constructor
  · exact fold_min_le_init _ _
  · intro i
    have h : minBias q ≤ min (q i) (1-q i) :=
      fold_min_le_mem _ 1 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    exact ⟨h.trans (min_le_left _ _), h.trans (min_le_right _ _)⟩

end Submod722.BernoulliProof

open NonmonotoneSubmod.Shared MeasureTheory
set_option autoImplicit false
theorem solution {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (f : Oracle (Fin ℓ))
    (hf : Submodular f) (h0 : 0 < f ∅) (q : Fin ℓ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    minBias q ≤ bernoulliProb q (fun S => f S ≠ 0)  := by
  have hc := Submod722.BernoulliProof.minBias_le q
  have h := Submod722.BernoulliProof.nonzero_bound q hq (minBias q) hc.1 hc.2
    Finset.univ f hf h0
  simpa [Submod722.BernoulliProof.prob, Submod722.BernoulliProof.weight,
    bernoulliProb] using h
