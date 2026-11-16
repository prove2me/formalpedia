-- Prove2me | solution 1 for DegreeSensitivity.full_sensitivity_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T17:26:51.901198+00:00
-- url     : https://prove2.me/submissions/65a052c4-81c9-4e86-acc7-1ec4d7408a4b

import Mathlib
import Definitions.Def_BoolFunc
import Definitions.Def_polyDegree
import Definitions.Def_sensitivity

open MvPolynomial
namespace DegreeNormal
noncomputable section
open Classical

lemma degree_substitute {n m : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (q : Fin n → MvPolynomial (Fin m) ℝ) (hq : ∀ i, (q i).totalDegree ≤ 1) :
    (eval₂ C q p).totalDegree ≤ p.totalDegree := by
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro d hd
  calc
    (C (p.coeff d) * ∏ i ∈ d.support, q i ^ d i).totalDegree
        ≤ (C (p.coeff d)).totalDegree + (∏ i ∈ d.support, q i ^ d i).totalDegree :=
      totalDegree_mul _ _
    _ = (∏ i ∈ d.support, q i ^ d i).totalDegree := by simp
    _ ≤ ∑ i ∈ d.support, (q i ^ d i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hq i))
    _ ≤ p.totalDegree := le_totalDegree hd

def lift {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) (y : Fin m → Bool) : Fin n → Bool :=
  fun i => if h : i ∈ t then if y (E ⟨i,h⟩) then !x i else x i else x i

lemma lift_zero {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m) (x : Fin n → Bool) :
    lift t E x (fun _ => false) = x := by
  funext i
  simp [lift]

lemma lift_unit {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) (j : Fin m) :
    lift t E x (Function.update (fun _ => false) j true) =
      flipBit x (E.symm j).val := by
  funext i
  by_cases hi : i ∈ t
  · have he : E ⟨i,hi⟩ = j ↔ i = (E.symm j).val := by
      constructor
      · intro h
        have := congrArg E.symm h
        simpa using congrArg Subtype.val this
      · intro h
        have h' : (⟨i,hi⟩ : t) = E.symm j := Subtype.ext h
        simpa [h']
    by_cases hij : i = (E.symm j).val
    · have hj : E ⟨i,hi⟩ = j := he.mpr hij
      simp [lift, hi, hj, flipBit, hij]
    · have hj : E ⟨i,hi⟩ ≠ j := fun h => hij (he.mp h)
      simp [lift, hi, Function.update_of_ne hj, flipBit, Function.update_of_ne hij]
  · have hij : i ≠ (E.symm j).val := by
      intro h
      exact hi (h ▸ (E.symm j).property)
    simp [lift, hi, flipBit, Function.update_of_ne hij]

def substitution {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) : Fin n → MvPolynomial (Fin m) ℝ :=
  fun i => if h : i ∈ t then if x i then 1 - X (E ⟨i,h⟩) else X (E ⟨i,h⟩)
    else C (if x i then 1 else 0)

lemma substitution_degree {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) (i : Fin n) : (substitution t E x i).totalDegree ≤ 1 := by
  unfold substitution
  split_ifs
  · exact (totalDegree_sub _ _).trans (by simp)
  · simp
  · simp
  · simp

lemma substitution_eval {n m : ℕ} (t : Finset (Fin n)) (E : t ≃ Fin m)
    (x : Fin n → Bool) (y : Fin m → Bool) (i : Fin n) :
    eval (fun j => if y j then (1:ℝ) else 0) (substitution t E x i) =
      if lift t E x y i then 1 else 0 := by
  by_cases hi : i ∈ t
  · cases hx : x i <;> cases hy : y (E ⟨i,hi⟩) <;> simp [substitution, lift, hi, hx, hy]
  · simp [substitution, lift, hi]

lemma normalized_degree {n m d : ℕ} (f : BoolFunc n) (hf : polyDegree f ≤ d)
    (t : Finset (Fin n)) (E : t ≃ Fin m) (x : Fin n → Bool) :
    polyDegree (fun y => if f x then !(f (lift t E x y)) else f (lift t E x y)) ≤ d := by
  obtain ⟨p,hp,hval⟩ := (show HasPolyRep f (polyDegree f) from Nat.find_spec _)
  let P := eval₂ C (substitution t E x) p
  have hP : P.totalDegree ≤ d :=
    (degree_substitute p _ (substitution_degree t E x)).trans (hp.trans hf)
  have hEval (y : Fin m → Bool) :
      eval (fun j => if y j then (1:ℝ) else 0) P = if f (lift t E x y) then 1 else 0 := by
    dsimp [P]
    rw [← eval_assoc]
    have he : (eval (fun j => if y j then (1:ℝ) else 0) ∘ substitution t E x) =
        (fun i => if lift t E x y i then (1:ℝ) else 0) := by
      funext i
      exact substitution_eval t E x y i
    rw [he]
    exact hval _
  apply Nat.find_min'
  refine ⟨if f x then 1-P else P, ?_, ?_⟩
  · split_ifs
    · exact (totalDegree_sub _ _).trans (by simpa using hP)
    · exact hP
  · intro y
    cases hx : f x <;> cases hy : f (lift t E x y) <;> simp [hx, hy, hEval y]

theorem normal_form :
    (∃ (n : ℕ) (f : BoolFunc n), polyDegree f ≤ 5 ∧ 14 ≤ sensitivity f) ↔
      ∃ g : BoolFunc 14, polyDegree g ≤ 5 ∧ g (fun _ => false) = false ∧
        ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true := by
  constructor
  · rintro ⟨n,f,hdeg,hs⟩
    obtain ⟨x,hx,hmax⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset (Fin n → Bool)) (by simp) (sensitivityAt f)
    have hcard : 14 ≤ (Finset.univ.filter (fun i => f (flipBit x i) ≠ f x)).card := by
      simpa [sensitivity, hmax, sensitivityAt] using hs
    obtain ⟨t,ht,hsize⟩ := Finset.exists_subset_card_eq hcard
    let E : t ≃ Fin 14 := t.equivFinOfCardEq hsize
    let g : BoolFunc 14 := fun y => if f x then !(f (lift t E x y)) else f (lift t E x y)
    refine ⟨g, normalized_degree f hdeg t E x, ?_, ?_⟩
    · simp [g, lift_zero]
    · intro j
      have hne : f (flipBit x (E.symm j).val) ≠ f x :=
        (Finset.mem_filter.mp (ht (E.symm j).property)).2
      dsimp [g]
      rw [lift_unit]
      cases hx : f x <;> cases hy : f (flipBit x (E.symm j).val) <;> simp_all
  · rintro ⟨g,hdeg,hzero,hunits⟩
    refine ⟨14,g,hdeg,?_⟩
    have hpoint : sensitivityAt g (fun _ => false) = 14 := by
      unfold sensitivityAt
      have hfilter : (Finset.univ.filter (fun i : Fin 14 =>
          g (flipBit (fun _ => false) i) ≠ g (fun _ => false))) = Finset.univ := by
        ext i
        simp [flipBit, hzero, hunits]
      rw [hfilter]
      simp
    calc
      14 = sensitivityAt g (fun _ => false) := hpoint.symm
      _ ≤ sensitivity g := Finset.le_sup (Finset.mem_univ _)

end
end DegreeNormal
theorem solution :
    (∃ (n : ℕ) (f : BoolFunc n), polyDegree f ≤ 5 ∧ 14 ≤ sensitivity f) ↔
      ∃ g : BoolFunc 14, polyDegree g ≤ 5 ∧ g (fun _ => false) = false ∧
        ∀ i : Fin 14, g (Function.update (fun _ => false) i true) = true :=
  DegreeNormal.normal_form
