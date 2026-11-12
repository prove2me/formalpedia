-- Prove2me | solution 1 for BunkbedAux.probOf_biUnion_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T03:59:09.9975+00:00
-- url     : https://prove2.me/submissions/ce8c3bf8-78f9-4bbb-8c51-468e21a9254b

import Definitions.Def_BunkbedPercolation

/-!
# Independence across edge-disjoint parts

Bernoulli bond percolation on a union of **pairwise disjoint** edge sets factors as a product
measure over the parts.  This is the percolation analogue of `Measure.pi` and the foundation of
the gadget-substitution argument.
-/

open Bunkbed Finset

set_option linter.unusedSectionVars false

namespace SubFactor

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-! ## Set-level lemmas -/

/-- If the `E i` are pairwise disjoint and `S i ⊆ E i`, then removing `⋃ S` from `⋃ E` can be
done part by part. -/
lemma sdiff_biUnion (E S : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (hsub : ∀ i, S i ⊆ E i) :
    (univ.biUnion E) \ (univ.biUnion S) = univ.biUnion (fun i => E i \ S i) := by
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hno⟩
    exact ⟨i, hi, fun h => hno ⟨i, h⟩⟩
  · rintro ⟨i, hi, hni⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    rintro ⟨j, hj⟩
    by_cases hij : j = i
    · rw [hij] at hj; exact hni hj
    · exact (Finset.disjoint_left.mp (hdisj i j (Ne.symm hij)) hi) (hsub j hj)

/-- Forward-backward: a tuple of parts is recovered from its union.  This is where disjointness
is used. -/
lemma biUnion_inter (E S : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (hsub : ∀ i, S i ⊆ E i) (i : iota) :
    (univ.biUnion S) ∩ E i = S i := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, hj⟩, hEi⟩
    by_cases hij : j = i
    · rw [hij] at hj; exact hj
    · exact absurd (hsub j hj) (Finset.disjoint_left.mp (hdisj i j (Ne.symm hij)) hEi)
  · intro h
    exact ⟨⟨i, h⟩, hsub i h⟩

/-- Backward-forward: a subset of `⋃ E` is recovered from its intersections with the parts. -/
lemma biUnion_inter_eq_self (E : iota → Finset (Sym2 V)) (T : Finset (Sym2 V))
    (hT : T ⊆ univ.biUnion E) :
    univ.biUnion (fun i => T ∩ E i) = T := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨i, h, -⟩; exact h
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hT h)
    exact ⟨i, h, hi⟩

/-- `⋃ S ⊆ ⋃ E` when `S i ⊆ E i`. -/
lemma biUnion_mono_pointwise (E S : iota → Finset (Sym2 V)) (hsub : ∀ i, S i ⊆ E i) :
    univ.biUnion S ⊆ univ.biUnion E := by
  intro e he
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hsub i hi⟩

/-! ## Milestone (a): the weight factors -/

/-- **Milestone (a).**  The percolation weight of a configuration assembled from pairwise
disjoint parts is the product of the weights of the parts. -/
lemma weight_biUnion (E S : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (hsub : ∀ i, S i ⊆ E i) (w : Sym2 V → ℚ) :
    weight (univ.biUnion E) w (univ.biUnion S) = ∏ i, weight (E i) w (S i) := by
  have hSd : (↑(univ : Finset iota) : Set iota).PairwiseDisjoint S := by
    intro i _ j _ hij
    simp only [Function.onFun]
    exact Finset.disjoint_of_subset_left (hsub i)
      (Finset.disjoint_of_subset_right (hsub j) (hdisj i j hij))
  have hEd : (↑(univ : Finset iota) : Set iota).PairwiseDisjoint (fun i => E i \ S i) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    exact Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset (hdisj i j hij))
  simp only [weight]
  rw [sdiff_biUnion E S hdisj hsub, Finset.prod_biUnion hSd, Finset.prod_biUnion hEd,
    ← Finset.prod_mul_distrib]

end SubFactor

open SubFactor

/-! ## Milestone (c): the full factorisation -/

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {iota : Type*} [Fintype iota]
    [DecidableEq iota] (E : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (w : Sym2 V → ℚ) (ev : Finset (Sym2 V) → Prop) [DecidablePred ev] :
    probOf (Finset.univ.biUnion E) w ev
      = ∑ S ∈ Fintype.piFinset (fun i => (E i).powerset),
          (∏ i, weight (E i) w (S i)) *
            (if ev (Finset.univ.biUnion (fun i => S i)) then (1 : ℚ) else 0) := by
  rw [probOf]
  refine Finset.sum_nbij' (i := fun T i => T ∩ E i) (j := fun S => univ.biUnion S)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    refine Fintype.mem_piFinset.mpr (fun i => Finset.mem_powerset.mpr ?_)
    exact Finset.inter_subset_right
  · intro S hS
    have hsub : ∀ i, S i ⊆ E i := fun i =>
      Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hS i)
    exact Finset.mem_powerset.mpr (biUnion_mono_pointwise E S hsub)
  · intro T hT
    exact biUnion_inter_eq_self E T (Finset.mem_powerset.mp hT)
  · intro S hS
    have hsub : ∀ i, S i ⊆ E i := fun i =>
      Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hS i)
    funext i
    exact biUnion_inter E S hdisj hsub i
  · intro T hT
    have hTsub : T ⊆ univ.biUnion E := Finset.mem_powerset.mp hT
    have hsub : ∀ i, T ∩ E i ⊆ E i := fun _ => Finset.inter_subset_right
    have hrec : univ.biUnion (fun i => T ∩ E i) = T := biUnion_inter_eq_self E T hTsub
    rw [hrec, ← weight_biUnion E (fun i => T ∩ E i) hdisj hsub w, hrec]
    by_cases h : ev T
    · simp [h]
    · simp [h]

#print axioms SubFactor.sdiff_biUnion
#print axioms SubFactor.biUnion_inter
#print axioms SubFactor.biUnion_inter_eq_self
#print axioms SubFactor.weight_biUnion
#print axioms solution
