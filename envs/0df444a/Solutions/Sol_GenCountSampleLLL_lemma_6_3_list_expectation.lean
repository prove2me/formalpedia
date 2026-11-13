-- Prove2me | solution 1 for GenCountSampleLLL.lemma_6_3_list_expectation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:43:07.603867+00:00
-- url     : https://prove2.me/submissions/21c8c801-f751-401f-bab6-96d9a33bac7a

import Definitions.Def_GenCountSampleLLL_insertionChain
import Theorems.Thm_GenCountSampleLLL_lemma_6_3
noncomputable section
open scoped Classical BigOperators
open GenCountSampleLLL

private theorem finite_law_transfer {Ω A : Type} [Fintype Ω] [Fintype A] [DecidableEq A]
    (w : Ω → ℝ) (f g : Ω → A) (P : Ω → Prop) [DecidablePred P] (q : ℝ)
    (h : ∀ a : A,
      (∑ ω, w ω * (if f ω = a ∧ P ω then (1 : ℝ) else 0)) =
      q * ∑ ω, w ω * (if g ω = a then (1 : ℝ) else 0))
    (φ : A → ℝ) :
    (∑ ω, w ω * (if P ω then φ (f ω) else 0)) =
      q * ∑ ω, w ω * φ (g ω) := by
  have hF (ω : Ω) : (if P ω then φ (f ω) else 0) =
      ∑ a : A, (if f ω = a ∧ P ω then (1 : ℝ) else 0) * φ a := by
    by_cases hp : P ω <;> simp [hp, eq_comm]
  have hG (ω : Ω) : φ (g ω) =
      ∑ a : A, (if g ω = a then (1 : ℝ) else 0) * φ a := by
    simp [eq_comm]
  simp_rw [hF, hG, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = (∑ ω, w ω * (if f ω = a ∧ P ω then (1 : ℝ) else 0)) * φ a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    _ = (q * ∑ ω, w ω * (if g ω = a then (1 : ℝ) else 0)) * φ a := by rw [h a]
    _ = _ := by
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      ring

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T)
    (φ : Finset (Finset (Fin I.m) × I.Assign) → ℝ) :
    (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
      (if (T,z) ∈ I.Llist D a ω then φ (I.Llist D a ω) else 0)) =
      I.nuU (I.UT D T) z *
      ∑ ω : I.ExpSpace, (I.expLaw ω).toReal * φ (I.Le D a (T,z) ω) := by
  have hlaw (L : Finset (Finset (Fin I.m) × I.Assign)) :
      (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
        (if I.Llist D a ω = L ∧ (T,z) ∈ I.Llist D a ω then (1 : ℝ) else 0)) =
      I.nuU (I.UT D T) z * ∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
        (if I.Le D a (T,z) ω = L then (1 : ℝ) else 0) :=
    (lemma_6_3 I D a T z hT hz).2 L
  have hp := finite_law_transfer (fun ω : I.ExpSpace => (I.expLaw ω).toReal)
    (I.Llist D a) (I.Le D a (T,z)) (fun ω => (T,z) ∈ I.Llist D a ω)
    (I.nuU (I.UT D T) z) hlaw φ
  exact hp

