-- Prove2me | solution 1 for BunkbedAux.bbProb_biUnion_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T04:15:12.725313+00:00
-- url     : https://prove2.me/submissions/74468a27-93de-4865-86e6-9927e2af3299

import Definitions.Def_BunkbedPercolation

/-!
# Bunkbed percolation factorises over edge-disjoint parts

`bbProb` percolates the two levels of the bunkbed independently.  When the base edge set is a
disjoint union `⋃ i, E i`, each of the two independent percolations factors over the parts
(`SubFactor.probOf_biUnion_disjoint`), so the *double* sum over subsets of `⋃ i, E i` becomes a
double sum over *tuples* of subsets of the parts.

The reusable engine is `Sub2BBFactor.sum_weight_biUnion`: for an arbitrary coefficient function
`F : Finset (Sym2 V) → ℚ`,
`∑ S ∈ (univ.biUnion E).powerset, F S * weight (univ.biUnion E) w S
  = ∑ S ∈ piFinset (fun i => (E i).powerset), F (univ.biUnion S) * ∏ i, weight (E i) w (S i)`.
Applied once in each summation variable this gives the statement for `bbProb`.
-/

open Bunkbed Finset

set_option linter.unusedSectionVars false

namespace Sub2BBFactor

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-! ## Set-level lemmas (copied from `Solutions/Sub_factor.lean`) -/

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

/-- Forward-backward: a tuple of parts is recovered from its union. -/
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

/-- The percolation weight of a configuration assembled from pairwise disjoint parts is the
product of the weights of the parts. -/
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

/-! ## The reusable one-variable sub-lemma -/

/-- **Reusable engine.**  A weighted sum over all subsets of a disjoint union `⋃ i, E i`
reindexes as a sum over *tuples* of subsets of the parts, with the weight factoring as a
product.  `F` is an arbitrary coefficient function. -/
lemma sum_weight_biUnion (E : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (w : Sym2 V → ℚ)
    (F : Finset (Sym2 V) → ℚ) :
    (∑ S ∈ (univ.biUnion E).powerset, F S * weight (univ.biUnion E) w S)
      = ∑ S ∈ Fintype.piFinset (fun i => (E i).powerset),
          F (univ.biUnion S) * ∏ i, weight (E i) w (S i) := by
  refine Finset.sum_nbij' (i := fun T i => T ∩ E i) (j := fun S => univ.biUnion S)
    ?_ ?_ ?_ ?_ ?_
  · intro T _
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_powerset.mpr Finset.inter_subset_right)
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

/-! ## The two-variable version -/

/-- Two independent percolations on a disjoint union reindex simultaneously. -/
lemma sum_sum_weight_biUnion (E : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (w : Sym2 V → ℚ)
    (G : Finset (Sym2 V) → Finset (Sym2 V) → ℚ) :
    (∑ S₀ ∈ (univ.biUnion E).powerset, ∑ S₁ ∈ (univ.biUnion E).powerset,
        G S₀ S₁ * weight (univ.biUnion E) w S₀ * weight (univ.biUnion E) w S₁)
      = ∑ S₀ ∈ Fintype.piFinset (fun i => (E i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (E i).powerset),
            G (univ.biUnion S₀) (univ.biUnion S₁)
              * (∏ i, weight (E i) w (S₀ i)) * ∏ i, weight (E i) w (S₁ i) := by
  have inner : ∀ S₀ : Finset (Sym2 V),
      (∑ S₁ ∈ (univ.biUnion E).powerset,
          G S₀ S₁ * weight (univ.biUnion E) w S₀ * weight (univ.biUnion E) w S₁)
        = (∑ S₁ ∈ (univ.biUnion E).powerset, G S₀ S₁ * weight (univ.biUnion E) w S₁)
            * weight (univ.biUnion E) w S₀ := by
    intro S₀
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun S₁ _ => by ring)
  have step1 :
      (∑ S₀ ∈ (univ.biUnion E).powerset, ∑ S₁ ∈ (univ.biUnion E).powerset,
          G S₀ S₁ * weight (univ.biUnion E) w S₀ * weight (univ.biUnion E) w S₁)
        = ∑ S₀ ∈ (univ.biUnion E).powerset,
            (∑ S₁ ∈ (univ.biUnion E).powerset, G S₀ S₁ * weight (univ.biUnion E) w S₁)
              * weight (univ.biUnion E) w S₀ :=
    Finset.sum_congr rfl (fun S₀ _ => inner S₀)
  have step2 :
      (∑ S₀ ∈ (univ.biUnion E).powerset,
          (∑ S₁ ∈ (univ.biUnion E).powerset, G S₀ S₁ * weight (univ.biUnion E) w S₁)
            * weight (univ.biUnion E) w S₀)
        = ∑ S₀ ∈ Fintype.piFinset (fun i => (E i).powerset),
            (∑ S₁ ∈ (univ.biUnion E).powerset,
                G (univ.biUnion S₀) S₁ * weight (univ.biUnion E) w S₁)
              * ∏ i, weight (E i) w (S₀ i) :=
    sum_weight_biUnion E hdisj w
      (fun S₀ => ∑ S₁ ∈ (univ.biUnion E).powerset, G S₀ S₁ * weight (univ.biUnion E) w S₁)
  rw [step1, step2]
  refine Finset.sum_congr rfl (fun S₀ _ => ?_)
  rw [sum_weight_biUnion E hdisj w (fun S₁ => G (univ.biUnion S₀) S₁), Finset.sum_mul]
  exact Finset.sum_congr rfl (fun S₁ _ => by ring)

end Sub2BBFactor

open Sub2BBFactor

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → Finset (Sym2 V)) (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (w : Sym2 V → ℚ) (T : Finset V) (x y : V × Fin 2) :
    bbProb (Finset.univ.biUnion E) w T x y
      = ∑ S₀ ∈ Fintype.piFinset (fun i => (E i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (E i).powerset),
            (if (bbGraph T (Finset.univ.biUnion (fun i => S₀ i))
                  (Finset.univ.biUnion (fun i => S₁ i))).Reachable x y then (1 : ℚ) else 0)
              * (∏ i, weight (E i) w (S₀ i)) * (∏ i, weight (E i) w (S₁ i)) := by
  rw [bbProb]
  exact sum_sum_weight_biUnion E hdisj w
    (fun S₀ S₁ => if (bbGraph T S₀ S₁).Reachable x y then (1 : ℚ) else 0)

#print axioms Sub2BBFactor.sum_weight_biUnion
#print axioms Sub2BBFactor.sum_sum_weight_biUnion
#print axioms solution
