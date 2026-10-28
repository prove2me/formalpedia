-- Prove2me | solution 1 for D1Bound5.IsD1.card_le_four_of_one_three_negative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:38:27.73498+00:00
-- url     : https://prove2.me/submissions/d553ec2a-d238-4b8a-9c2b-b62997971b92

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_full_ring_one_three_negative_extension
import Theorems.Thm_D1Bound5_full_ring_three_negative_odd_impossible

section
open scoped NumberField
open Module

namespace D1Bound5



























/-- Complete negative-entry branch of the manuscript's {1,3} lemma, over
all imaginary quadratic full rings. The extra entry may be -1. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {A : Finset (𝓞 K)} (hA : IsD1 A)
    (h1 : (1 : 𝓞 K) ∈ A) (h3 : (3 : 𝓞 K) ∈ A)
    (hn : ∃ n : ℤ, n<0 ∧ (n : 𝓞 K) ∈ A) : A.card ≤ 4 := by
  classical
  obtain ⟨n,hn,hnA⟩ := hn
  have hn1 : (1 : 𝓞 K) ≠ (n : 𝓞 K) := by
    intro h
    have he : (1 : ℤ)=n := Int.cast_injective (by simpa using h)
    omega
  have hn3 : (3 : 𝓞 K) ≠ (n : 𝓞 K) := by
    intro h
    have he : (3 : ℤ)=n := Int.cast_injective (by simpa using h)
    omega
  have hnr : ∃ r : 𝓞 K, r*r = (n : 𝓞 K)+1 := by
    simpa only [one_mul] using hA.2 1 h1 n hnA hn1
  have hns := hA.2 3 h3 n hnA hn3
  let B := (A.erase 1).erase 3
  have hb (z : 𝓞 K) (hz : z ∈ B) :
      z ∈ A ∧ z ≠ 1 ∧ z ≠ 3 := by
    simp only [B, Finset.mem_erase] at hz
    exact ⟨hz.2.2,hz.2.1,hz.1⟩
  have hneg (z : 𝓞 K) (hz : z ∈ B) :
      ∃ p : ℤ, z=(p : 𝓞 K) ∧ p<0 ∧ p%2=1 := by
    obtain ⟨hzA,hz1,hz3⟩ := hb z hz
    apply full_ring_one_three_negative_extension hK hn hnr hns (hA.1 z hzA)
    · simpa only [one_mul] using hA.2 1 h1 z hzA hz1.symm
    · exact hA.2 3 h3 z hzA hz3.symm
    · by_cases he : z=(n : 𝓞 K)
      · exact Or.inl he
      · exact Or.inr (hA.2 z hzA n hnA he)
  have hB : B.card ≤ 2 := by
    by_contra hle
    obtain ⟨C,hCB,hCcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ B.card by omega)
    let e : Fin 3 ≃ C := (Fintype.equivFinOfCardEq (by simpa using hCcard)).symm
    let f : Fin 3 → 𝓞 K := fun i => (e i).val
    have hf (i : Fin 3) : f i ∈ B := hCB (e i).property
    have hinj : Function.Injective f := by
      intro i j hij
      apply e.injective
      exact Subtype.ext hij
    obtain ⟨x,hx,hxn,hxo⟩ := hneg (f 0) (hf 0)
    obtain ⟨y,hy,hyn,hyo⟩ := hneg (f 1) (hf 1)
    obtain ⟨z,hz,hzn,hzo⟩ := hneg (f 2) (hf 2)
    have hpair (i j : Fin 3) (hij : i ≠ j) :
        ∃ r : 𝓞 K, r*r = f i*f j+1 :=
      hA.2 (f i) (hb (f i) (hf i)).1 (f j) (hb (f j) (hf j)).1
        (fun h => hij (hinj h))
    apply full_ring_three_negative_odd_impossible hK x y z hxn hyn hzn hxo hyo hzo
    · simpa only [hx,hy] using hpair 0 1 (by decide)
    · simpa only [hx,hz] using hpair 0 2 (by decide)
    · simpa only [hy,hz] using hpair 1 2 (by decide)
  have hc1 := Finset.card_erase_add_one h1
  have h3' : (3 : 𝓞 K) ∈ A.erase 1 := by
    exact Finset.mem_erase.mpr ⟨by norm_num,h3⟩
  have hc3 := Finset.card_erase_add_one h3'
  dsimp [B] at hB
  omega



end D1Bound5
end
