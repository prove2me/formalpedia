-- Prove2me | solution 1 for Disjunctive.IntroDuality.regularity_condition_necessary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:36:12.713281+00:00
-- url     : https://prove2.me/submissions/67907122-6efe-4c86-a67c-42b47466553a

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_PolyhedralSystems
import Definitions.Def_Disjunctive_IntroDuality_RegularityCondition
import Theorems.Thm_SteinitzExchange_Duality_farkas_affine_form1

open Disjunctive.IntroDuality

namespace DRegAux

theorem lp_attain {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hX : (PolyNonneg A b).Nonempty) (hU : (DualPoly A c).Nonempty) :
    ∃ x ∈ PolyNonneg A b, ∀ y ∈ PolyNonneg A b, dotProduct c x ≤ dotProduct c y := by
  classical
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨u, hu⟩ := hU
  have hlow : ∀ x ∈ PolyNonneg A b, dotProduct u b ≤ dotProduct c x := by
    intro x hx
    calc dotProduct u b ≤ dotProduct u (A.mulVec x) :=
          dotProduct_le_dotProduct_of_nonneg_left (fun i => hx.1 i) hu.2
      _ = dotProduct (Matrix.vecMul u A) x := Matrix.dotProduct_mulVec _ _ _
      _ ≤ dotProduct c x := dotProduct_le_dotProduct_of_nonneg_right (fun j => hu.1 j) hx.2
  set S := (fun x => dotProduct c x) '' PolyNonneg A b with hS
  have hbdd : BddBelow S := ⟨dotProduct u b, by rintro _ ⟨x, hx, rfl⟩; exact hlow x hx⟩
  have hne : S.Nonempty := ⟨_, x0, hx0, rfl⟩
  set v := sInf S with hvdef
  have hv : ∀ x ∈ PolyNonneg A b, v ≤ dotProduct c x := fun x hx => csInf_le hbdd ⟨x, hx, rfl⟩
  let a : (Fin m ⊕ (Fin n ⊕ Unit)) → Fin n → ℝ := fun i => match i with
    | Sum.inl i => fun j => -A i j
    | Sum.inr (Sum.inl k) => fun j => if j = k then -1 else 0
    | Sum.inr (Sum.inr _) => c
  let r : (Fin m ⊕ (Fin n ⊕ Unit)) → ℝ := fun i => match i with
    | Sum.inl i => -b i
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr _) => v
  rcases SteinitzExchange.Duality.farkas_affine_form1 a r with ⟨x, hx⟩ | ⟨y, hy0, -, hcol, hneg⟩
  · have hxX : x ∈ PolyNonneg A b := by
      refine ⟨fun i => ?_, fun k => ?_⟩
      · have := hx (Sum.inl i)
        simp only [a, r, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] at this
        simpa [Matrix.mulVec, dotProduct] using this
      · have := hx (Sum.inr (Sum.inl k))
        simp only [a, r, ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          if_true] at this
        show (0:ℝ) ≤ x k
        linarith
    refine ⟨x, hxX, fun z hz => ?_⟩
    have := hx (Sum.inr (Sum.inr ()))
    simp only [a, r] at this
    exact le_trans (by simpa [dotProduct] using this) (hv z hz)
  · exfalso
    set t := y (Sum.inr (Sum.inr ()))
    have ht : 0 ≤ t := hy0 _
    have key : ∀ x ∈ PolyNonneg A b,
        ∑ i, y (Sum.inl i) * b i ≤ t * dotProduct c x := by
      intro x hx
      have h0 : ∑ i, y i * ∑ j, a i j * x j = 0 := by
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hcol]
        simp
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h0
      have h1 : ∑ i, y (Sum.inl i) * ∑ j, a (Sum.inl i) j * x j ≤ -∑ i, y (Sum.inl i) * b i := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro i _
        have hi := hx.1 i
        simp only [Matrix.mulVec, dotProduct] at hi
        have e : ∑ j, a (Sum.inl i) j * x j = -∑ j, A i j * x j := by
          simp [a, Finset.sum_neg_distrib]
        rw [e]
        nlinarith [hy0 (Sum.inl i)]
      have h2 : ∑ k, y (Sum.inr (Sum.inl k)) * ∑ j, a (Sum.inr (Sum.inl k)) j * x j ≤ 0 := by
        apply Finset.sum_nonpos
        intro k _
        simp only [a, ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact mul_nonpos_of_nonneg_of_nonpos (hy0 _) (neg_nonpos.2 (hx.2 k))
      have h3 : ∑ k : Unit, y (Sum.inr (Sum.inr k)) * ∑ j, a (Sum.inr (Sum.inr k)) j * x j
          = t * dotProduct c x := by
        simp [a, t, dotProduct]
      linarith
    have hneg' : -∑ i, y (Sum.inl i) * b i + t * v < 0 := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hneg
      simp only [r, mul_neg, Finset.sum_neg_distrib, mul_zero, Finset.sum_const_zero,
        add_zero] at hneg
      simpa [t] using hneg
    rcases ht.lt_or_eq with htp | ht0
    · have : (∑ i, y (Sum.inl i) * b i) / t ≤ v := by
        apply le_csInf hne
        rintro _ ⟨x, hx, rfl⟩
        rw [div_le_iff₀ htp]; linarith [key x hx]
      rw [div_le_iff₀ htp] at this
      linarith
    · have := key x0 hx0
      rw [← ht0] at this hneg'
      linarith

end DRegAux

theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) (c : Fin n → ℝ)
    (hNotReg : ¬ RegularityCondition
                  (FeasibleIndices (fun h => PolyNonneg (A h) (b h)))
                  (FeasibleIndices (fun h => DualPoly (A h) c)))
    (hDP : (⋃ h : Q, PolyNonneg (A h) (b h)).Nonempty)
    (hDD : ¬ ∃ w : ℝ, ∃ u : (h : Q) → Fin (m h) → ℝ,
              ∀ h, u h ∈ DualPoly (A h) c ∧ w ≤ dotProduct (u h) (b h)) :
    ∃ v : ℝ, IsLeast ((fun x => dotProduct c x) '' (⋃ h : Q, PolyNonneg (A h) (b h))) v := by
  classical
  have hsub : ∀ h, (PolyNonneg (A h) (b h)).Nonempty → (DualPoly (A h) c).Nonempty := by
    intro h hh
    by_contra hc
    apply hNotReg
    intro _
    exact ⟨h, hh, hc⟩
  obtain ⟨x0, hx0⟩ := hDP
  obtain ⟨h0, hh0⟩ := Set.mem_iUnion.1 hx0
  let F := Finset.univ.filter (fun h => (PolyNonneg (A h) (b h)).Nonempty)
  have hF : F.Nonempty := ⟨h0, by simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x0, hh0⟩⟩
  have hm : ∀ h ∈ F, ∃ x ∈ PolyNonneg (A h) (b h),
      ∀ y ∈ PolyNonneg (A h) (b h), dotProduct c x ≤ dotProduct c y := by
    intro h hh
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    exact DRegAux.lp_attain (A h) (b h) c hh (hsub h hh)
  choose! xs hxsX hxsmin using hm
  obtain ⟨h1, hh1, hmin⟩ := F.exists_min_image (fun h => dotProduct c (xs h)) hF
  refine ⟨dotProduct c (xs h1), ⟨xs h1, Set.mem_iUnion.2 ⟨h1, hxsX h1 hh1⟩, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨h, hxh⟩ := Set.mem_iUnion.1 hx
  have hhF : h ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x, hxh⟩
  exact (hmin h hhF).trans (hxsmin h hhF x hxh)
