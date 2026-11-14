-- Prove2me | solution 1 for FiniteSampleDependence.Rigidity.maximal_minor_saturation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T20:26:53.696288+00:00
-- url     : https://prove2.me/submissions/81bd63b0-81b5-4930-a41e-3d4836ba7a49

import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra
import Mathlib

section
section
/-!
# The prefix order on finite subsets

This file contains the finite combinatorics used by the straightening law for
minors.  For subsets `A B` of `Fin N`, the relation `A ≼ B` means that every
initial segment contains at least as many elements of `A` as of `B`.

The definition uses initial segments of lengths `r : Fin (N + 1)`.  In
particular, the last value records the cardinality of the entire subset; this
also makes the definition uniform when `N = 0`.
-/

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

/-- The number of elements of `A` in the first `r` positions of `Fin N`. -/
def prefixCard {N : ℕ} (A : Finset (Fin N)) (r : Fin (N + 1)) : ℕ :=
  (A.filter fun i ↦ i.val < r.val).card

/-- The standard order on finite subsets used for standard bitableaux. -/
def PrefixLE {N : ℕ} (A B : Finset (Fin N)) : Prop :=
  ∀ r : Fin (N + 1), prefixCard B r ≤ prefixCard A r

scoped infix:50 " ≼ₚ " => PrefixLE

lemma prefixLE_refl {N : ℕ} (A : Finset (Fin N)) : A ≼ₚ A := by
  intro r
  exact le_rfl

lemma prefixLE_trans {N : ℕ} {A B C : Finset (Fin N)}
    (hAB : A ≼ₚ B) (hBC : B ≼ₚ C) : A ≼ₚ C := by
  intro r
  exact (hBC r).trans (hAB r)

lemma prefixCard_last {N : ℕ} (A : Finset (Fin N)) :
    prefixCard A (Fin.last N) = A.card := by
  simp [prefixCard, Fin.last]

lemma card_ge_of_prefixLE {N : ℕ} {A B : Finset (Fin N)}
    (h : A ≼ₚ B) : B.card ≤ A.card := by
  simpa [prefixCard_last] using h (Fin.last N)

lemma prefixLE_of_superset {N : ℕ} {A B : Finset (Fin N)}
    (hBA : B ⊆ A) : A ≼ₚ B := by
  intro r
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hBA hi.1, hi.2⟩

/-- The prefix ending immediately before `i`. -/
def prefixBefore {N : ℕ} (i : Fin N) : Fin (N + 1) :=
  ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- The prefix ending at `i`. -/
def prefixThrough {N : ℕ} (i : Fin N) : Fin (N + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

lemma prefixCard_through {N : ℕ} (A : Finset (Fin N)) (i : Fin N) :
    prefixCard A (prefixThrough i) =
      prefixCard A (prefixBefore i) + if i ∈ A then 1 else 0 := by
  have hfilter :
      A.filter (fun j ↦ j.val < (prefixThrough i).val) =
        if i ∈ A then
          insert i (A.filter fun j ↦ j.val < (prefixBefore i).val)
        else A.filter fun j ↦ j.val < (prefixBefore i).val := by
    ext j
    by_cases hji : j = i
    · subst j
      by_cases hiA : i ∈ A <;> simp [hiA, prefixThrough, prefixBefore]
    · have hval : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
      by_cases hiA : i ∈ A <;>
        simp [hiA, hji, prefixThrough, prefixBefore] <;> omega
  rw [prefixCard, prefixCard, hfilter]
  by_cases hiA : i ∈ A
  · simp [hiA, prefixBefore]
  · simp [hiA]

/-- The prefix immediately before the `q`-th element of a finite subset has
exactly `q` elements. -/
lemma prefixCard_before_orderEmbOfFin {N : ℕ} (A : Finset (Fin N))
    (q : Fin A.card) :
    prefixCard A (prefixBefore (A.orderEmbOfFin rfl q)) = q.val := by
  let e : Fin A.card ↪ Fin N := (A.orderEmbOfFin rfl).toEmbedding
  have hfilter :
      A.filter (fun j ↦ j.val < (A.orderEmbOfFin rfl q).val) =
        (Finset.Iio q).map e := by
    ext j
    constructor
    · intro hj
      have hjA : j ∈ A := (Finset.mem_filter.mp hj).1
      have hjAset : j ∈ (A : Set (Fin N)) := hjA
      rw [← A.range_orderEmbOfFin rfl] at hjAset
      obtain ⟨k, rfl⟩ := hjAset
      apply Finset.mem_map.mpr
      refine ⟨k, ?_, rfl⟩
      exact Finset.mem_Iio.mpr
        ((A.orderEmbOfFin rfl).lt_iff_lt.mp (Finset.mem_filter.mp hj).2)
    · intro hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
      apply Finset.mem_filter.mpr
      exact ⟨A.orderEmbOfFin_mem rfl k,
        (A.orderEmbOfFin rfl).lt_iff_lt.mpr (Finset.mem_Iio.mp hk)⟩
  rw [prefixCard, prefixBefore, hfilter, Finset.card_map, Fin.card_Iio]

/-- If `b` lies strictly before the `q`-th element of `A`, then at most `q`
elements of `A` occur at or before `b`. -/
lemma prefixCard_through_le_index_of_lt_orderEmbOfFin {N : ℕ}
    (A : Finset (Fin N)) (q : Fin A.card) (b : Fin N)
    (hb : b < A.orderEmbOfFin rfl q) :
    prefixCard A (prefixThrough b) ≤ q.val := by
  calc
    prefixCard A (prefixThrough b) ≤
        prefixCard A (prefixBefore (A.orderEmbOfFin rfl q)) := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, by
        simp only [prefixThrough, prefixBefore] at hj ⊢
        omega⟩
    _ = q.val := prefixCard_before_orderEmbOfFin A q

/-- Prefix dominance implies the usual componentwise comparison of the
increasing enumerations.  This is the direction needed to recover a standard
bitableau from its diagonal monomial. -/
lemma orderEmbOfFin_le_of_prefixLE {N : ℕ} {A B : Finset (Fin N)}
    (hAB : A ≼ₚ B) (q : Fin B.card) :
    A.orderEmbOfFin rfl (Fin.castLE (card_ge_of_prefixLE hAB) q) ≤
      B.orderEmbOfFin rfl q := by
  let qA : Fin A.card := Fin.castLE (card_ge_of_prefixLE hAB) q
  let a := A.orderEmbOfFin rfl qA
  let b := B.orderEmbOfFin rfl q
  by_contra hnot
  have hba : b < a := lt_of_not_ge hnot
  have hB : prefixCard B (prefixThrough b) = q.val + 1 := by
    rw [prefixCard_through]
    simp only [b, B.orderEmbOfFin_mem, if_true]
    rw [prefixCard_before_orderEmbOfFin]
  have hA : prefixCard A (prefixThrough b) ≤ q.val := by
    have := prefixCard_through_le_index_of_lt_orderEmbOfFin A qA b hba
    simpa [qA] using this
  have hdom := hAB (prefixThrough b)
  rw [hB] at hdom
  omega

lemma eq_of_prefixCard_eq {N : ℕ} {A B : Finset (Fin N)}
    (h : ∀ r : Fin (N + 1), prefixCard A r = prefixCard B r) : A = B := by
  ext i
  have hbefore := h (prefixBefore i)
  have hthrough := h (prefixThrough i)
  rw [prefixCard_through A i, prefixCard_through B i, hbefore] at hthrough
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;>
    simp_all

lemma prefixLE_antisymm {N : ℕ} {A B : Finset (Fin N)}
    (hAB : A ≼ₚ B) (hBA : B ≼ₚ A) : A = B := by
  apply eq_of_prefixCard_eq
  intro r
  exact Nat.le_antisymm (hBA r) (hAB r)

/-- The rank used to turn strict descent in the prefix order into descent in
the natural numbers. -/
def prefixRank {N : ℕ} (A : Finset (Fin N)) : ℕ :=
  ∑ r : Fin (N + 1), prefixCard A r

lemma prefixRank_mono {N : ℕ} {A B : Finset (Fin N)}
    (h : A ≼ₚ B) : prefixRank B ≤ prefixRank A := by
  unfold prefixRank
  exact Finset.sum_le_sum fun r _ ↦ h r

lemma prefixRank_lt_of_prefixLE_of_exists_lt {N : ℕ}
    {A B : Finset (Fin N)} (h : A ≼ₚ B)
    (hstrict : ∃ r : Fin (N + 1), prefixCard B r < prefixCard A r) :
    prefixRank B < prefixRank A := by
  rcases hstrict with ⟨r, hr⟩
  unfold prefixRank
  exact Finset.sum_lt_sum (fun i _ ↦ h i) ⟨r, Finset.mem_univ r, hr⟩

lemma exists_prefixCard_lt_of_prefixLE_of_ne {N : ℕ}
    {A B : Finset (Fin N)} (h : A ≼ₚ B) (hne : A ≠ B) :
    ∃ r : Fin (N + 1), prefixCard B r < prefixCard A r := by
  by_contra hnot
  push Not at hnot
  apply hne
  apply eq_of_prefixCard_eq
  intro r
  exact Nat.le_antisymm (hnot r) (h r)

lemma prefixRank_lt_of_prefixLE_of_ne {N : ℕ}
    {A B : Finset (Fin N)} (h : A ≼ₚ B) (hne : A ≠ B) :
    prefixRank B < prefixRank A :=
  prefixRank_lt_of_prefixLE_of_exists_lt h
    (exists_prefixCard_lt_of_prefixLE_of_ne h hne)

/-- Strict prefix order. -/
def PrefixLT {N : ℕ} (A B : Finset (Fin N)) : Prop := A ≼ₚ B ∧ A ≠ B

scoped infix:50 " ≺ₚ " => PrefixLT

/-- Defect from the largest possible prefix rank.  Moving strictly downward
in the prefix order strictly decreases this natural number. -/
def prefixDefect {N : ℕ} (A : Finset (Fin N)) : ℕ :=
  prefixRank (Finset.univ : Finset (Fin N)) - prefixRank A

lemma prefixRank_le_univ {N : ℕ} (A : Finset (Fin N)) :
    prefixRank A ≤ prefixRank (Finset.univ : Finset (Fin N)) := by
  exact prefixRank_mono (prefixLE_of_superset (Finset.subset_univ A))

lemma prefixDefect_lt_of_prefixLT {N : ℕ} {A B : Finset (Fin N)}
    (h : A ≺ₚ B) : prefixDefect A < prefixDefect B := by
  have hrank : prefixRank B < prefixRank A :=
    prefixRank_lt_of_prefixLE_of_ne h.1 h.2
  have hbound := prefixRank_le_univ A
  unfold prefixDefect
  omega

lemma prefixDefect_le_of_prefixLE {N : ℕ} {A B : Finset (Fin N)}
    (h : A ≼ₚ B) : prefixDefect A ≤ prefixDefect B := by
  have hrank := prefixRank_mono h
  have hbound := prefixRank_le_univ A
  unfold prefixDefect
  omega

/-- The additive defect used for induction on a pair of row/column subsets. -/
def laplaceDefect {N : ℕ} (A B : Finset (Fin N)) : ℕ :=
  prefixDefect A + prefixDefect B

lemma laplaceDefect_comm {N : ℕ} (A B : Finset (Fin N)) :
    laplaceDefect A B = laplaceDefect B A := by
  simp [laplaceDefect, add_comm]

lemma laplaceDefect_lt_of_left_strict {N : ℕ}
    {A B A' B' : Finset (Fin N)}
    (hA : A' ≺ₚ A) (hB : B' ≼ₚ B) :
    laplaceDefect A' B' < laplaceDefect A B := by
  unfold laplaceDefect
  exact Nat.add_lt_add_of_lt_of_le
    (prefixDefect_lt_of_prefixLT hA) (prefixDefect_le_of_prefixLE hB)

lemma laplaceDefect_lt_of_right_strict {N : ℕ}
    {A B A' B' : Finset (Fin N)}
    (hA : A' ≼ₚ A) (hB : B' ≺ₚ B) :
    laplaceDefect A' B' < laplaceDefect A B := by
  unfold laplaceDefect
  exact Nat.add_lt_add_of_le_of_lt
    (prefixDefect_le_of_prefixLE hA) (prefixDefect_lt_of_prefixLT hB)

end GenericMaximalMinor

end
end
end

section
section
/-!
# Generic minors over a commutative coefficient ring

The primaryness induction changes the coefficient ring after localizing at a
corner variable.  Consequently the determinantal definitions used by that
induction must be polymorphic in the coefficient ring, even though the final
probability application has real coefficients.

An index for a minor stores its size and the increasing row and column
embeddings.  The size is bounded by `min n m`, so the type of all minors is
finite and includes the empty minor.
-/

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

abbrev GenericVar (n m : ℕ) := Fin n × Fin m

abbrev GenericPoly (D : Type*) [CommSemiring D] (n m : ℕ) :=
  MvPolynomial (GenericVar n m) D

/-- An arbitrary minor of an `n × m` matrix, including the empty minor. -/
structure MinorIndex (n m : ℕ) where
  size : Fin (min n m + 1)
  rows : Fin size.val ↪o Fin n
  cols : Fin size.val ↪o Fin m

instance minorIndexDecidableEq (n m : ℕ) : DecidableEq (MinorIndex n m) :=
  Classical.decEq _

/-- The set of rows selected by a minor. -/
def MinorIndex.rowSet {n m : ℕ} (d : MinorIndex n m) : Finset (Fin n) :=
  Finset.univ.map d.rows.toEmbedding

/-- The set of columns selected by a minor. -/
def MinorIndex.colSet {n m : ℕ} (d : MinorIndex n m) : Finset (Fin m) :=
  Finset.univ.map d.cols.toEmbedding

@[simp] lemma MinorIndex.card_rowSet {n m : ℕ} (d : MinorIndex n m) :
    d.rowSet.card = d.size.val := by
  simp [MinorIndex.rowSet]

@[simp] lemma MinorIndex.card_colSet {n m : ℕ} (d : MinorIndex n m) :
    d.colSet.card = d.size.val := by
  simp [MinorIndex.colSet]

/-- The standard partial order on minors: both row and column sets are in the
prefix order. -/
def MinorLE {n m : ℕ} (d e : MinorIndex n m) : Prop :=
  d.rowSet ≼ₚ e.rowSet ∧ d.colSet ≼ₚ e.colSet

scoped infix:50 " ≼ₘ " => MinorLE

/-- The square matrix whose determinant is the indicated generic minor. -/
def minorMatrix {D : Type*} [CommRing D] {n m : ℕ} (d : MinorIndex n m) :
    Matrix (Fin d.size.val) (Fin d.size.val) (GenericPoly D n m) :=
  fun i j ↦ MvPolynomial.X (d.rows i, d.cols j)

/-- A minor of the generic `n × m` matrix. -/
def minorPoly {D : Type*} [CommRing D] {n m : ℕ} (d : MinorIndex n m) :
    GenericPoly D n m :=
  Matrix.det (minorMatrix d)

/-- The canonical minor index associated to a maximal set of columns. -/
def maximalIndex {n m : ℕ} (hnm : n ≤ m) (S : Fin n ↪o Fin m) :
    MinorIndex n m where
  size := ⟨n, by omega⟩
  rows := OrderEmbedding.id (Fin n)
  cols := S

abbrev MaximalMinorIndex (n m : ℕ) := Fin n ↪o Fin m

/-- A maximal minor over an arbitrary commutative coefficient ring. -/
def maximalMinorPolyOver {D : Type*} [CommRing D] {n m : ℕ}
    (hnm : n ≤ m) (S : MaximalMinorIndex n m) : GenericPoly D n m :=
  minorPoly (maximalIndex hnm S)

/-- The ideal generated by the maximal minors of a generic `n × m` matrix. -/
def maximalMinorIdealOver (D : Type*) [CommRing D]
    (n m : ℕ) (hnm : n ≤ m) : Ideal (GenericPoly D n m) :=
  Ideal.span (Set.range (maximalMinorPolyOver (D := D) hnm))

lemma maximalMinorPolyOver_mem_ideal {D : Type*} [CommRing D]
    {n m : ℕ} (hnm : n ≤ m) (S : MaximalMinorIndex n m) :
    maximalMinorPolyOver (D := D) hnm S ∈
      maximalMinorIdealOver D n m hnm := by
  apply Ideal.subset_span
  exact Set.mem_range_self S

end GenericMaximalMinor

end
end
end

section
section
/-!
# The permutation form of generalized Laplace exchange

We first prove the combinatorial exchange identity for the permutation
expansion of a Laplace product.  The later determinant file identifies this
permutation sum with the signed product of complementary minors.  Keeping the
two arguments separate makes all reindexing and inclusion-exclusion steps
independent of determinant APIs.
-/

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

section Permutations

variable {N : ℕ}

/-- Image of a finite subset under a permutation. -/
def permImage (s : Equiv.Perm (Fin N)) (A : Finset (Fin N)) : Finset (Fin N) :=
  A.map s.toEmbedding

/-- Preimage of a finite subset under a permutation. -/
def permPreimage (s : Equiv.Perm (Fin N)) (A : Finset (Fin N)) : Finset (Fin N) :=
  A.map s.symm.toEmbedding

@[simp] lemma mem_permImage_iff (s : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) (i : Fin N) :
    i ∈ permImage s A ↔ s.symm i ∈ A := by
  simp [permImage]

@[simp] lemma mem_permPreimage_iff (s : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) (i : Fin N) :
    i ∈ permPreimage s A ↔ s i ∈ A := by
  simp [permPreimage]

@[simp] lemma permImage_permPreimage (s : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) : permImage s (permPreimage s A) = A := by
  ext i
  simp

@[simp] lemma permPreimage_permImage (s : Equiv.Perm (Fin N))
    (A : Finset (Fin N)) : permPreimage s (permImage s A) = A := by
  ext i
  simp

lemma permPreimage_subset_iff (s : Equiv.Perm (Fin N))
    (A B : Finset (Fin N)) :
    permPreimage s A ⊆ B ↔ A ⊆ permImage s B := by
  constructor
  · intro h i hi
    simp only [mem_permImage_iff]
    apply h
    simpa using hi
  · intro h i hi
    simp only [mem_permPreimage_iff] at hi
    have himage := h hi
    simpa using himage

lemma permImage_eq_iff_eq_permPreimage (s : Equiv.Perm (Fin N))
    (A B : Finset (Fin N)) :
    permImage s A = B ↔ A = permPreimage s B := by
  constructor
  · intro h
    rw [← h, permPreimage_permImage]
  · rintro rfl
    exact permImage_permPreimage s B

end Permutations

section Exchange

variable {N R : Type*} [Fintype N] [DecidableEq N] [CommRing R]

/-- The determinant monomial in mathlib's row-permuting convention. -/
def determinantPermutationTerm (Y : Matrix N N R) (s : Equiv.Perm N) : R :=
  (Equiv.Perm.sign s : R) * ∏ i : N, Y (s i) i

end Exchange

section FinExchange

variable {N : ℕ} {R : Type*} [CommRing R]

/-- Permutation expansion of the signed Laplace product indexed by `A,B`. -/
def laplacePermSum (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) : R :=
  ∑ s : Equiv.Perm (Fin N),
    if permImage s B = A then determinantPermutationTerm Y s else 0

/-- The matrix obtained by deleting the two off-diagonal blocks determined by
the row set `A` and column set `B`. -/
def maskedMatrix (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) : Matrix (Fin N) (Fin N) R :=
  fun i j ↦ if (i ∈ A ↔ j ∈ B) then Y i j else 0

lemma permImage_eq_iff_forall_membership (s : Equiv.Perm (Fin N))
    (A B : Finset (Fin N)) :
    permImage s B = A ↔ ∀ i, (s i ∈ A ↔ i ∈ B) := by
  constructor
  · intro h i
    rw [← h]
    simp
  · intro h
    ext i
    simpa using (h (s.symm i)).symm

lemma determinantPermutationTerm_maskedMatrix
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (s : Equiv.Perm (Fin N)) :
    determinantPermutationTerm (maskedMatrix Y A B) s =
      if permImage s B = A then determinantPermutationTerm Y s else 0 := by
  classical
  by_cases h : permImage s B = A
  · have hall := (permImage_eq_iff_forall_membership s A B).mp h
    simp only [determinantPermutationTerm, maskedMatrix]
    simp_rw [if_pos (hall _)]
    rw [if_pos h]
  · have hex : ∃ i, ¬(s i ∈ A ↔ i ∈ B) := by
      by_contra hn
      push Not at hn
      exact h ((permImage_eq_iff_forall_membership s A B).mpr hn)
    rcases hex with ⟨i, hi⟩
    rw [if_neg h]
    unfold determinantPermutationTerm
    have hfactor : maskedMatrix Y A B (s i) i = 0 := by
      simp [maskedMatrix, hi]
    have hprod : ∏ j : Fin N, maskedMatrix Y A B (s j) j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hfactor
    rw [hprod, mul_zero]

lemma laplacePermSum_eq_det_maskedMatrix
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    laplacePermSum Y A B = Matrix.det (maskedMatrix Y A B) := by
  classical
  rw [laplacePermSum, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro s _
  exact (determinantPermutationTerm_maskedMatrix Y A B s).symm

/-- All subsets of `Fin N` containing `A`. -/
def supersets (A : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  Finset.univ.powerset.filter fun U ↦ A ⊆ U

@[simp] lemma mem_supersets_iff (A U : Finset (Fin N)) :
    U ∈ supersets A ↔ A ⊆ U := by
  simp [supersets]

lemma sum_laplacePermSum_subsets (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) :
    (∑ V ∈ B.powerset, laplacePermSum Y A V) =
      ∑ s : Equiv.Perm (Fin N),
        if A ⊆ permImage s B then determinantPermutationTerm Y s else 0 := by
  classical
  simp_rw [laplacePermSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : A ⊆ permImage s B
  · have hmem : permPreimage s A ∈ B.powerset := by
      rw [Finset.mem_powerset, permPreimage_subset_iff]
      exact hs
    rw [if_pos hs, Finset.sum_eq_single (permPreimage s A)]
    · simp
    · intro V hV hne
      rw [if_neg]
      intro heq
      apply hne
      exact (permImage_eq_iff_eq_permPreimage s V A).mp heq
    · exact fun hnot ↦ (hnot hmem).elim
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro V hV
    rw [if_neg]
    intro heq
    apply hs
    apply (permPreimage_subset_iff s A B).mp
    rw [← (permImage_eq_iff_eq_permPreimage s V A).mp heq]
    exact Finset.mem_powerset.mp hV

lemma sum_laplacePermSum_supersets (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) :
    (∑ U ∈ supersets A, laplacePermSum Y U B) =
      ∑ s : Equiv.Perm (Fin N),
        if A ⊆ permImage s B then determinantPermutationTerm Y s else 0 := by
  classical
  simp_rw [laplacePermSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : A ⊆ permImage s B
  · have hmem : permImage s B ∈ supersets A := by
      exact (mem_supersets_iff A (permImage s B)).mpr hs
    rw [if_pos hs, Finset.sum_eq_single (permImage s B)]
    · simp
    · intro U hU hne
      rw [if_neg]
      exact fun heq ↦ hne heq.symm
    · exact fun hnot ↦ (hnot hmem).elim
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro U hU
    rw [if_neg]
    intro heq
    apply hs
    rw [heq]
    exact (mem_supersets_iff A U).mp hU

/-- Generalized Laplace exchange in permutation form. -/
theorem laplacePermSum_exchange (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) :
    (∑ V ∈ B.powerset, laplacePermSum Y A V) =
      ∑ U ∈ supersets A, laplacePermSum Y U B := by
  rw [sum_laplacePermSum_subsets, sum_laplacePermSum_supersets]

end FinExchange

end GenericMaximalMinor

end
end
end

section
section
/-!
# A masked determinant as a signed product of complementary minors

The exchange argument is most convenient when a Laplace product is represented
by a masked determinant.  This file supplies the exact bridge back to a product
of two minors.  We deliberately retain the sign of the column permutation
instead of expanding it into a formula involving sums of indices: its value is
a unit over every commutative ring, which is precisely what straightening needs.
-/

noncomputable section

namespace GenericMaximalMinor

open scoped BigOperators

variable {N : ℕ} {R : Type*} [CommRing R]

/-- The minor with row subtype `p` and column subtype `q`, after identifying
the two subtype index sets by `e`. -/
def minorAlongEquiv (Y : Matrix (Fin N) (Fin N) R)
    {p q : Fin N → Prop} [DecidablePred p] [DecidablePred q]
    (e : {i // p i} ≃ {j // q j}) : R :=
  Matrix.det fun (i : {i // p i}) (j : {i // p i}) ↦ Y i (e j)

/-- The order-preserving identification of two equally large subsets, obtained
by enumerating both in increasing order. -/
def orderedFinsetEquiv (A B : Finset (Fin N)) (h : A.card = B.card) : A ≃ B :=
  (A.orderIsoOfFin rfl).symm.toEquiv.trans (B.orderIsoOfFin h.symm).toEquiv

/-- The canonical minor selected by two finite subsets.  It is zero when the
row and column cardinalities differ. -/
def finsetMinor (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) : R :=
  if h : A.card = B.card then minorAlongEquiv Y (orderedFinsetEquiv A B h) else 0

@[simp] lemma finsetMinor_of_card_ne (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) (h : A.card ≠ B.card) :
    finsetMinor Y A B = 0 := by
  simp [finsetMinor, h]

lemma minorAlongEquiv_eq_sign_mul_finsetMinor
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card = B.card) (e : A ≃ B) :
    minorAlongEquiv Y e =
      (@Equiv.Perm.sign A _ (Subtype.fintype (fun i : Fin N ↦ i ∈ A))
          (e.trans (orderedFinsetEquiv A B hcard).symm) : R) *
        finsetMinor Y A B := by
  classical
  letI : Fintype A := Subtype.fintype (fun i : Fin N ↦ i ∈ A)
  let eo : A ≃ B := orderedFinsetEquiv A B hcard
  let s : Equiv.Perm A := e.trans eo.symm
  have hmatrix :
      (fun (i : A) (j : A) ↦ Y i (e j)) =
        (fun (i : A) (j : A) ↦ Y i (eo (s j))) := by
    funext i j
    simp [s, eo]
  rw [finsetMinor, dif_pos hcard]
  unfold minorAlongEquiv
  rw [hmatrix]
  change Matrix.det
    (Matrix.submatrix (Matrix.of (fun (i : A) (j : A) ↦ Y i (eo j))) id s) = _
  rw [Matrix.det_permute']
  rfl

lemma maskedMatrix_apply_extendSubtype_of_mem
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (e : {i // i ∈ A} ≃ {j // j ∈ B}) (i j : {i // i ∈ A}) :
    maskedMatrix Y A B i (e.extendSubtype j) = Y i (e j) := by
  rw [Equiv.extendSubtype_apply_of_mem e j j.property]
  simp [maskedMatrix, i.property, (e j).property]

lemma maskedMatrix_apply_extendSubtype_of_not_mem
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (e : {i // i ∈ A} ≃ {j // j ∈ B})
    (i j : {i // ¬i ∈ A}) :
    maskedMatrix Y A B i (e.extendSubtype j) = Y i (e.toCompl j) := by
  rw [Equiv.extendSubtype_apply_of_not_mem e j j.property]
  change
    (if ((i : Fin N) ∈ A ↔ (e.toCompl j : Fin N) ∈ B)
      then Y i (e.toCompl j) else 0) = Y i (e.toCompl j)
  rw [if_pos]
  exact ⟨fun hi ↦ (i.property hi).elim, fun hj ↦ ((e.toCompl j).property hj).elim⟩

/-- Exact block-determinant form of the Laplace-product expansion.  The sign
is the sign of the permutation extending the chosen equivalence `A ≃ B`.
No ordering formula for that sign is needed later. -/
theorem sign_mul_det_maskedMatrix_eq_mul_minors
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (e : {i // i ∈ A} ≃ {j // j ∈ B}) :
    (Equiv.Perm.sign e.extendSubtype : R) * Matrix.det (maskedMatrix Y A B) =
      minorAlongEquiv Y e * minorAlongEquiv Y e.toCompl := by
  classical
  let M : Matrix (Fin N) (Fin N) R :=
    (maskedMatrix Y A B).submatrix id e.extendSubtype
  have hzero : ∀ i, i ∈ A → ∀ j, ¬j ∈ A → M i j = 0 := by
    intro i hi j hj
    simp only [M, Matrix.submatrix_apply, id_eq]
    have hnotB := Equiv.extendSubtype_not_mem e j hj
    simp [maskedMatrix, hi, hnotB]
  have hblocks := Matrix.twoBlockTriangular_det' M (fun i ↦ i ∈ A) hzero
  have hleft :
      @Matrix.det _ _ (Subtype.fintype (fun i : Fin N ↦ i ∈ A)) R _
          (Matrix.toSquareBlockProp M (fun i ↦ i ∈ A)) =
        minorAlongEquiv Y e := by
    unfold minorAlongEquiv
    refine congrArg
      (fun X : Matrix {i : Fin N // i ∈ A} {i : Fin N // i ∈ A} R ↦
        @Matrix.det _ _ (Subtype.fintype (fun i : Fin N ↦ i ∈ A)) R _ X) ?_
    funext i j
    exact maskedMatrix_apply_extendSubtype_of_mem Y A B e i j
  have hright :
      @Matrix.det _ _ (Subtype.fintype (fun i : Fin N ↦ ¬i ∈ A)) R _
          (Matrix.toSquareBlockProp M (fun i ↦ ¬i ∈ A)) =
        minorAlongEquiv Y e.toCompl := by
    unfold minorAlongEquiv
    refine congrArg
      (fun X : Matrix {i : Fin N // ¬i ∈ A} {i : Fin N // ¬i ∈ A} R ↦
        @Matrix.det _ _ (Subtype.fintype (fun i : Fin N ↦ ¬i ∈ A)) R _ X) ?_
    funext i j
    exact maskedMatrix_apply_extendSubtype_of_not_mem Y A B e i j
  have hblockprod :
      Matrix.det M = minorAlongEquiv Y e * minorAlongEquiv Y e.toCompl :=
    hblocks.trans (congrArg₂ (· * ·) hleft hright)
  calc
    (Equiv.Perm.sign e.extendSubtype : R) * Matrix.det (maskedMatrix Y A B) =
        Matrix.det M := by
      exact (Matrix.det_permute' e.extendSubtype (maskedMatrix Y A B)).symm
    _ = minorAlongEquiv Y e * minorAlongEquiv Y e.toCompl := hblockprod

end GenericMaximalMinor

end
end
end

section
section
/-!
# Inclusion--exclusion consequences of generalized Laplace exchange

This file isolates the finite-set Möbius inversion used by both branches of
Laplace straightening.  It is stated over an arbitrary commutative ring so the
same theorem can later be specialized to integer coefficients and to generic
polynomial rings.
-/

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

variable {α R : Type*} [DecidableEq α] [CommRing R]

lemma sum_powerset_neg_one_pow_card_cast (S : Finset α) :
    (∑ W ∈ S.powerset, (-1 : R) ^ W.card) = if S = ∅ then 1 else 0 := by
  have h := Finset.sum_powerset_neg_one_pow_card (x := S)
  have hcast := congrArg (Int.castRingHom R) h
  simpa using hcast

lemma sum_powerset_sdiff (B W : Finset α) (f : Finset α → R) :
    (∑ V ∈ (B \ W).powerset, f V) =
      ∑ V ∈ B.powerset, if Disjoint V W then f V else 0 := by
  classical
  have hfilter :
      (B \ W).powerset = B.powerset.filter fun V ↦ Disjoint V W := by
    ext V
    simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_sdiff]
  rw [hfilter, Finset.sum_filter]

/-- The two natural descriptions of the disjoint pairs `(W,V)` occurring in
finite-set inclusion--exclusion. -/
lemma sum_powerset_sdiff_swap (C B : Finset α) (f : Finset α → Finset α → R) :
    (∑ W ∈ C.powerset, ∑ V ∈ (B \ W).powerset, f W V) =
      ∑ V ∈ B.powerset, ∑ W ∈ (C \ V).powerset, f W V := by
  classical
  simp_rw [sum_powerset_sdiff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V _
  apply Finset.sum_congr rfl
  intro W _
  by_cases h : Disjoint V W
  · simp [h, h.symm]
  · have h' : ¬Disjoint W V := fun hw ↦ h hw.symm
    simp [h, h']

/-- Finite-set Möbius filtering: alternating over the elements forbidden from
`V` retains precisely the terms with `C ⊆ V`. -/
theorem powerset_mobius_filter (C B : Finset α) (_hCB : C ⊆ B)
    (f : Finset α → R) :
    (∑ W ∈ C.powerset, (-1 : R) ^ W.card *
        ∑ V ∈ (B \ W).powerset, f V) =
      ∑ V ∈ B.powerset, if C ⊆ V then f V else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [sum_powerset_sdiff_swap C B (fun W V ↦ (-1 : R) ^ W.card * f V)]
  apply Finset.sum_congr rfl
  intro V hVB
  rw [← Finset.sum_mul]
  rw [sum_powerset_neg_one_pow_card_cast]
  by_cases hCV : C ⊆ V
  · have hempty : C \ V = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hCV
    rw [if_pos hempty, if_pos hCV, one_mul]
  · have hnonempty : C \ V ≠ ∅ := by
      exact fun h ↦ hCV (Finset.sdiff_eq_empty_iff_subset.mp h)
    rw [if_neg hnonempty, if_neg hCV, zero_mul]

section Laplace

variable {N : ℕ}

/-- Subsets lying in the interval `[C,B]` of the inclusion poset. -/
def betweenSubsets (C B : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  B.powerset.filter fun V ↦ C ⊆ V

@[simp] lemma mem_betweenSubsets_iff (C B V : Finset (Fin N)) :
    V ∈ betweenSubsets C B ↔ C ⊆ V ∧ V ⊆ B := by
  simp [betweenSubsets, and_comm]

/-- First inclusion--exclusion form of generalized Laplace exchange. -/
theorem laplacePermSum_exchange_inclusionExclusion_one
    (Y : Matrix (Fin N) (Fin N) R)
    (A B C : Finset (Fin N)) (hCB : C ⊆ B) :
    (∑ V ∈ betweenSubsets C B, laplacePermSum Y A V) =
      ∑ U ∈ supersets A, ∑ W ∈ C.powerset,
        (-1 : R) ^ W.card * laplacePermSum Y U (B \ W) := by
  classical
  symm
  calc
    (∑ U ∈ supersets A, ∑ W ∈ C.powerset,
        (-1 : R) ^ W.card * laplacePermSum Y U (B \ W)) =
        ∑ W ∈ C.powerset, (-1 : R) ^ W.card *
          ∑ U ∈ supersets A, laplacePermSum Y U (B \ W) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = ∑ W ∈ C.powerset, (-1 : R) ^ W.card *
          ∑ V ∈ (B \ W).powerset, laplacePermSum Y A V := by
      apply Finset.sum_congr rfl
      intro W _
      congr 1
      exact (laplacePermSum_exchange Y A (B \ W)).symm
    _ = ∑ V ∈ B.powerset,
          if C ⊆ V then laplacePermSum Y A V else 0 :=
      powerset_mobius_filter C B hCB (laplacePermSum Y A)
    _ = ∑ V ∈ betweenSubsets C B, laplacePermSum Y A V := by
      rw [betweenSubsets, Finset.sum_filter]

end Laplace

end GenericMaximalMinor

end
end
end

section
section
/-!
# Straightening signed Laplace products

The induction measure and exchange identities have already been separated into
earlier files.  Here we develop the good/bad subset reductions used by the
Laplace straightening theorem.
-/

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

variable {N : ℕ} {R : Type*} [CommRing R]

/-- A subset is good when it precedes its complement in prefix order. -/
def GoodSubset (A : Finset (Fin N)) : Prop := A ≼ₚ Aᶜ

lemma laplacePermSum_eq_zero_of_card_ne
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card ≠ B.card) : laplacePermSum Y A B = 0 := by
  classical
  rw [laplacePermSum]
  apply Finset.sum_eq_zero
  intro s _
  rw [if_neg]
  intro heq
  apply hcard
  rw [← heq]
  simp [permImage]

lemma maskedMatrix_transpose
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    maskedMatrix Y.transpose B A = (maskedMatrix Y A B).transpose := by
  ext i j
  simp only [maskedMatrix, Matrix.transpose_apply]
  by_cases hi : i ∈ B <;> by_cases hj : j ∈ A <;> simp [hi, hj]

lemma laplacePermSum_transpose
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    laplacePermSum Y.transpose B A = laplacePermSum Y A B := by
  rw [laplacePermSum_eq_det_maskedMatrix, laplacePermSum_eq_det_maskedMatrix,
    maskedMatrix_transpose, Matrix.det_transpose]

/-- The prefix of `Fin N` selected by `r`. -/
def prefixFinset (r : Fin (N + 1)) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ i.val < r.val

@[simp] lemma mem_prefixFinset_iff (r : Fin (N + 1)) (i : Fin N) :
    i ∈ prefixFinset r ↔ i.val < r.val := by
  simp [prefixFinset]

lemma prefixCard_eq_card_inter (A : Finset (Fin N)) (r : Fin (N + 1)) :
    prefixCard A r = (A ∩ prefixFinset r).card := by
  unfold prefixCard
  apply congrArg Finset.card
  ext i
  simp [prefixFinset, and_comm]

lemma prefixFinset_mono {r s : Fin (N + 1)} (hrs : r.val ≤ s.val) :
    prefixFinset r ⊆ prefixFinset s := by
  intro i hi
  simp only [mem_prefixFinset_iff] at hi ⊢
  omega

lemma exists_bad_prefix {B : Finset (Fin N)} (hbad : ¬GoodSubset B) :
    ∃ r : Fin (N + 1), prefixCard B r < prefixCard Bᶜ r := by
  by_contra h
  push Not at h
  apply hbad
  intro r
  exact h r

/-- Small complementary elements at a bad prefix. -/
def exchangeLow (B : Finset (Fin N)) (r : Fin (N + 1)) : Finset (Fin N) :=
  Bᶜ ∩ prefixFinset r

/-- Elements of `B` at or above the chosen prefix cut. -/
def exchangeHigh (B : Finset (Fin N)) (r : Fin (N + 1)) : Finset (Fin N) :=
  B \ prefixFinset r

/-- The enlarged ambient set used in the large-cardinality exchange relation. -/
def exchangeAmbient (B : Finset (Fin N)) (r : Fin (N + 1)) : Finset (Fin N) :=
  B ∪ exchangeLow B r

/-- The set of entries which the inclusion--exclusion relation may remove. -/
def exchangeRemoval (B : Finset (Fin N)) (r : Fin (N + 1)) : Finset (Fin N) :=
  exchangeLow B r ∪ exchangeHigh B r

lemma exchangeRemoval_subset_exchangeAmbient (B : Finset (Fin N))
    (r : Fin (N + 1)) : exchangeRemoval B r ⊆ exchangeAmbient B r := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_right _ hi
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hi).1

lemma card_lt_exchangeRemoval_of_bad_prefix {B : Finset (Fin N)}
    {r : Fin (N + 1)} (hbad : prefixCard B r < prefixCard Bᶜ r) :
    B.card < (exchangeRemoval B r).card := by
  have hdis : Disjoint (exchangeLow B r) (exchangeHigh B r) := by
    rw [Finset.disjoint_left]
    intro i hiLow hiHigh
    exact (Finset.mem_sdiff.mp hiHigh).2 (Finset.mem_inter.mp hiLow).2
  have hlow : (exchangeLow B r).card = prefixCard Bᶜ r := by
    rw [prefixCard_eq_card_inter]
    rfl
  have hhigh : (exchangeHigh B r).card = B.card - prefixCard B r := by
    rw [exchangeHigh, Finset.card_sdiff, Finset.inter_comm,
      ← prefixCard_eq_card_inter]
  rw [exchangeRemoval, Finset.card_union_of_disjoint hdis, hlow, hhigh]
  have hprefix : prefixCard B r ≤ B.card := by
    unfold prefixCard
    exact Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- Replacing sufficiently many high elements of `B` by the smaller
complementary elements below a bad prefix moves downward in prefix order. -/
lemma exchange_result_prefixLE (B : Finset (Fin N)) (r : Fin (N + 1))
    (W : Finset (Fin N)) (hW : W ⊆ exchangeRemoval B r)
    (hcard : B.card ≤ (exchangeAmbient B r \ W).card) :
    exchangeAmbient B r \ W ≼ₚ B := by
  intro s
  let E := exchangeAmbient B r \ W
  by_cases hsr : s.val ≤ r.val
  · have hprefix : prefixFinset s ⊆ prefixFinset r := prefixFinset_mono hsr
    have hsub : B ∩ prefixFinset s ⊆ E ∩ prefixFinset s := by
      intro i hi
      have hiB : i ∈ B := (Finset.mem_inter.mp hi).1
      have hiS : i ∈ prefixFinset s := (Finset.mem_inter.mp hi).2
      have hiD : i ∈ exchangeAmbient B r := by
        exact Finset.mem_union_left _ hiB
      have hiW : i ∉ W := by
        intro hiWin
        have hiC := hW hiWin
        rcases Finset.mem_union.mp hiC with hiLow | hiHigh
        · exact (Finset.mem_compl.mp (Finset.mem_inter.mp hiLow).1) hiB
        · exact (Finset.mem_sdiff.mp hiHigh).2 (hprefix hiS)
      exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hiD, hiW⟩, hiS⟩
    rw [prefixCard_eq_card_inter, prefixCard_eq_card_inter]
    exact Finset.card_le_card hsub
  · have hrs : r.val ≤ s.val := by omega
    have hprefix : prefixFinset r ⊆ prefixFinset s := prefixFinset_mono hrs
    have hout : E \ prefixFinset s ⊆ B \ prefixFinset s := by
      intro i hi
      have hiE : i ∈ E := (Finset.mem_sdiff.mp hi).1
      have hiNotS : i ∉ prefixFinset s := (Finset.mem_sdiff.mp hi).2
      have hiD : i ∈ exchangeAmbient B r := (Finset.mem_sdiff.mp hiE).1
      have hiB : i ∈ B := by
        rcases Finset.mem_union.mp hiD with hiB | hiLow
        · exact hiB
        · have hiR : i ∈ prefixFinset r := (Finset.mem_inter.mp hiLow).2
          exact (hiNotS (hprefix hiR)).elim
      exact Finset.mem_sdiff.mpr ⟨hiB, hiNotS⟩
    have houtCard : (E \ prefixFinset s).card ≤ (B \ prefixFinset s).card :=
      Finset.card_le_card hout
    have hpartE := Finset.card_inter_add_card_sdiff E (prefixFinset s)
    have hpartB := Finset.card_inter_add_card_sdiff B (prefixFinset s)
    rw [prefixCard_eq_card_inter, prefixCard_eq_card_inter]
    dsimp only [E] at hpartE houtCard ⊢
    omega

lemma exchangeAmbient_sdiff_exchangeLow (B : Finset (Fin N))
    (r : Fin (N + 1)) :
    exchangeAmbient B r \ exchangeLow B r = B := by
  ext i
  by_cases hiB : i ∈ B
  · simp [exchangeAmbient, exchangeLow, hiB]
  · simp [exchangeAmbient, exchangeLow, hiB]

lemma exchangeAmbient_sdiff_eq_iff (B : Finset (Fin N))
    (r : Fin (N + 1)) (W : Finset (Fin N))
    (hW : W ⊆ exchangeRemoval B r) :
    exchangeAmbient B r \ W = B ↔ W = exchangeLow B r := by
  constructor
  · intro hE
    ext i
    constructor
    · intro hiW
      have hiC := hW hiW
      rcases Finset.mem_union.mp hiC with hiLow | hiHigh
      · exact hiLow
      · have hiB := (Finset.mem_sdiff.mp hiHigh).1
        have hiD : i ∈ exchangeAmbient B r := Finset.mem_union_left _ hiB
        have hiDiff : i ∈ exchangeAmbient B r \ W :=
          hE.symm ▸ hiB
        exact ((Finset.mem_sdiff.mp hiDiff).2 hiW).elim
    · intro hiLow
      by_contra hiNotW
      have hiD : i ∈ exchangeAmbient B r := Finset.mem_union_right _ hiLow
      have hiDiff : i ∈ exchangeAmbient B r \ W :=
        Finset.mem_sdiff.mpr ⟨hiD, hiNotW⟩
      have hiB : i ∈ B := hE ▸ hiDiff
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hiLow).1) hiB
  · rintro rfl
    exact exchangeAmbient_sdiff_exchangeLow B r

/-- Values of good Laplace products bounded by `A,B` in prefix order. -/
def laplaceStraighteningGenerators
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) : Set R :=
  {x | ∃ A' B', A' ≼ₚ A ∧ B' ≼ₚ B ∧ GoodSubset A' ∧ GoodSubset B' ∧
    x = laplacePermSum Y A' B'}

/-- Integral span of the good bounded Laplace products.  `AddSubgroup.closure`
is exactly the ℤ-linear span inside the additive group of `R`. -/
def laplaceStraighteningSpan
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) : AddSubgroup R :=
  AddSubgroup.closure (laplaceStraighteningGenerators Y A B)

lemma laplacePermSum_mem_straighteningSpan_of_good
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hA : GoodSubset A) (hB : GoodSubset B) :
    laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B := by
  apply AddSubgroup.subset_closure
  exact ⟨A, B, prefixLE_refl A, prefixLE_refl B, hA, hB, rfl⟩

lemma zero_mem_laplaceStraighteningSpan
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    (0 : R) ∈ laplaceStraighteningSpan Y A B :=
  (laplaceStraighteningSpan Y A B).zero_mem

lemma negOnePow_mul_mem_laplaceStraighteningSpan_iff
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (k : ℕ) (x : R) :
    (-1 : R) ^ k * x ∈ laplaceStraighteningSpan Y A B ↔
      x ∈ laplaceStraighteningSpan Y A B := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have heq : (-1 : R) ^ k * -1 * x = -((-1 : R) ^ k * x) := by ring
      rw [heq, (laplaceStraighteningSpan Y A B).neg_mem_iff, ih]

lemma laplaceStraighteningSpan_mono
    (Y : Matrix (Fin N) (Fin N) R)
    {A B A' B' : Finset (Fin N)} (hA : A' ≼ₚ A) (hB : B' ≼ₚ B) :
    laplaceStraighteningSpan Y A' B' ≤ laplaceStraighteningSpan Y A B := by
  apply AddSubgroup.closure_mono
  intro x hx
  rcases hx with ⟨C, D, hCA, hDB, hC, hD, rfl⟩
  exact ⟨C, D, prefixLE_trans hCA hA, prefixLE_trans hDB hB, hC, hD, rfl⟩

lemma laplaceStraighteningSpan_transpose
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    laplaceStraighteningSpan Y.transpose B A = laplaceStraighteningSpan Y A B := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases hx with ⟨B', A', hBB, hAA, hB', hA', rfl⟩
    rw [laplacePermSum_transpose]
    apply AddSubgroup.subset_closure
    exact ⟨A', B', hAA, hBB, hA', hB', rfl⟩
  · apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases hx with ⟨A', B', hAA, hBB, hA', hB', rfl⟩
    rw [← laplacePermSum_transpose]
    apply AddSubgroup.subset_closure
    exact ⟨B', A', hBB, hAA, hB', hA', rfl⟩

lemma AddSubgroup.mem_of_sum_eq_zero_of_mem_erase
    (H : AddSubgroup R) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R) (a : ι) (ha : a ∈ s)
    (hsum : ∑ x ∈ s, f x = 0)
    (hmem : ∀ x ∈ s.erase a, f x ∈ H) : f a ∈ H := by
  have herase : (∑ x ∈ s.erase a, f x) ∈ H := H.sum_mem fun x hx ↦ hmem x hx
  have hsplit := Finset.add_sum_erase s f ha
  have hneg : f a = -(∑ x ∈ s.erase a, f x) := by
    rw [hsum] at hsplit
    exact eq_neg_of_add_eq_zero_left hsplit
  rw [hneg]
  exact H.neg_mem herase

/-- Unified bad-second-coordinate reduction.  Unlike the paper's presentation,
this construction works in every cardinality range, so no `2p < N`/`2p ≥ N`
case split is needed. -/
lemma laplacePermSum_mem_straighteningSpan_of_bad_right
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card = B.card) (hbad : ¬GoodSubset B)
    (ih : ∀ A' B' : Finset (Fin N),
      laplaceDefect A' B' < laplaceDefect A B →
        laplacePermSum Y A' B' ∈ laplaceStraighteningSpan Y A' B') :
    laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B := by
  classical
  obtain ⟨r, hr⟩ := exists_bad_prefix hbad
  let J := exchangeLow B r
  let D := exchangeAmbient B r
  let C := exchangeRemoval B r
  let S := supersets A ×ˢ C.powerset
  let f : Finset (Fin N) × Finset (Fin N) → R := fun q ↦
    (-1 : R) ^ q.2.card * laplacePermSum Y q.1 (D \ q.2)
  have hCD : C ⊆ D := exchangeRemoval_subset_exchangeAmbient B r
  have hCcard : A.card < C.card := by
    rw [hcard]
    exact card_lt_exchangeRemoval_of_bad_prefix hr
  have hleft :
      (∑ V ∈ betweenSubsets C D, laplacePermSum Y A V) = 0 := by
    apply Finset.sum_eq_zero
    intro V hV
    apply laplacePermSum_eq_zero_of_card_ne
    have hCV : C ⊆ V := (mem_betweenSubsets_iff C D V).mp hV |>.1
    have hle : C.card ≤ V.card := Finset.card_le_card hCV
    omega
  have htotal : ∑ q ∈ S, f q = 0 := by
    rw [Finset.sum_product]
    change (∑ U ∈ supersets A, ∑ W ∈ C.powerset,
      (-1 : R) ^ W.card * laplacePermSum Y U (D \ W)) = 0
    rw [← laplacePermSum_exchange_inclusionExclusion_one Y A D C hCD, hleft]
  have hJ : J ∈ C.powerset := by
    rw [Finset.mem_powerset]
    intro i hi
    exact Finset.mem_union_left _ hi
  have hAJ : (A, J) ∈ S := by
    exact Finset.mem_product.mpr ⟨(mem_supersets_iff A A).mpr (by rfl), hJ⟩
  have hother : ∀ q ∈ S.erase (A, J),
      f q ∈ laplaceStraighteningSpan Y A B := by
    intro q hq
    have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
    have hqne : q ≠ (A, J) := (Finset.mem_erase.mp hq).1
    rcases q with ⟨U, W⟩
    have hqProd : U ∈ supersets A ∧ W ∈ C.powerset :=
      Finset.mem_product.mp hqS
    have hAU : A ⊆ U := (mem_supersets_iff A U).mp hqProd.1
    have hWC : W ⊆ C := Finset.mem_powerset.mp hqProd.2
    let E := D \ W
    by_cases hUE : U.card = E.card
    · have hAcardU : A.card ≤ U.card := Finset.card_le_card hAU
      have hBcardE : B.card ≤ E.card := by omega
      have hEle : E ≼ₚ B := by
        exact exchange_result_prefixLE B r W hWC hBcardE
      have hUle : U ≼ₚ A := prefixLE_of_superset hAU
      have hdef : laplaceDefect U E < laplaceDefect A B := by
        by_cases hUA : U = A
        · have hWJ : W ≠ J := by
            intro hW
            exact hqne (Prod.ext hUA hW)
          have hEB : E ≠ B := by
            intro hE
            apply hWJ
            exact (exchangeAmbient_sdiff_eq_iff B r W hWC).mp hE
          exact laplaceDefect_lt_of_right_strict hUle ⟨hEle, hEB⟩
        · exact laplaceDefect_lt_of_left_strict ⟨hUle, hUA⟩ hEle
      have hterm := ih U E hdef
      have hterm' : laplacePermSum Y U E ∈ laplaceStraighteningSpan Y A B :=
        laplaceStraighteningSpan_mono Y hUle hEle hterm
      exact (negOnePow_mul_mem_laplaceStraighteningSpan_iff
        Y A B W.card (laplacePermSum Y U E)).mpr hterm'
    · have hzero : laplacePermSum Y U E = 0 :=
        laplacePermSum_eq_zero_of_card_ne Y U E hUE
      simp [f, E, hzero]
  have hdist : f (A, J) ∈ laplaceStraighteningSpan Y A B :=
    GenericMaximalMinor.AddSubgroup.mem_of_sum_eq_zero_of_mem_erase
      (laplaceStraighteningSpan Y A B) S f (A, J) hAJ htotal hother
  have hDB : D \ J = B := exchangeAmbient_sdiff_exchangeLow B r
  change (-1 : R) ^ J.card * laplacePermSum Y A (D \ J) ∈
    laplaceStraighteningSpan Y A B at hdist
  rw [hDB] at hdist
  exact (negOnePow_mul_mem_laplaceStraighteningSpan_iff
    Y A B J.card (laplacePermSum Y A B)).mp hdist

/-- Laplace straightening: every signed Laplace product is an integral linear
combination of bounded products whose two indexing subsets are good. -/
theorem laplacePermSum_mem_straighteningSpan
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N)) :
    laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B := by
  classical
  generalize hd : laplaceDefect A B = d
  induction d using Nat.strong_induction_on generalizing Y A B with
  | h d ih =>
      by_cases hcard : A.card = B.card
      · by_cases hA : GoodSubset A
        · by_cases hB : GoodSubset B
          · exact laplacePermSum_mem_straighteningSpan_of_good Y A B hA hB
          · exact laplacePermSum_mem_straighteningSpan_of_bad_right
              Y A B hcard hB fun A' B' hlt ↦
                ih (laplaceDefect A' B') (hlt.trans_eq hd) Y A' B' rfl
        · have ht :
              laplacePermSum Y.transpose B A ∈
                laplaceStraighteningSpan Y.transpose B A :=
            laplacePermSum_mem_straighteningSpan_of_bad_right
              Y.transpose B A hcard.symm hA fun B' A' hlt ↦
                ih (laplaceDefect B' A')
                  (hlt.trans_eq ((laplaceDefect_comm B A).trans hd))
                  Y.transpose B' A' rfl
          rw [laplacePermSum_transpose, laplaceStraighteningSpan_transpose] at ht
          exact ht
      · rw [laplacePermSum_eq_zero_of_card_ne Y A B hcard]
        exact zero_mem_laplaceStraighteningSpan Y A B

end GenericMaximalMinor

end
end
end

section
section
/-!
# Duplicating two ordered finite subsets

The rectangular two-minor argument places a tagged copy of each of two row
sets into one finite linear order.  Equal underlying values are ordered with
the left copy first.  This file packages that construction independently of
determinants.
-/

noncomputable section

namespace GenericMaximalMinor

/-- Tagged disjoint union of two finite subsets.

This is a wrapper rather than an abbreviation for `S ⊕ T`: `Sum` already has
an unrelated order instance, whereas below we need the order induced by the
underlying value first and the tag second. -/
structure DuplicatedSubset {n : ℕ} (S T : Finset (Fin n)) where
  toSum : S ⊕ T
  deriving DecidableEq

/-- The tagged union is equivalent to the ordinary disjoint union. -/
def duplicatedEquivSum {n : ℕ} (S T : Finset (Fin n)) :
    DuplicatedSubset S T ≃ S ⊕ T where
  toFun := DuplicatedSubset.toSum
  invFun := DuplicatedSubset.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance {n : ℕ} (S T : Finset (Fin n)) : Fintype (DuplicatedSubset S T) :=
  Fintype.ofEquiv (S ⊕ T) (duplicatedEquivSum S T).symm

/-- Forget the tag of an element in a duplicated subset. -/
def duplicatedValue {n : ℕ} {S T : Finset (Fin n)} :
    DuplicatedSubset S T → Fin n
  | ⟨Sum.inl i⟩ => i
  | ⟨Sum.inr i⟩ => i

/-- Left tags precede right tags when the underlying values agree. -/
def duplicatedTag {n : ℕ} {S T : Finset (Fin n)} :
    DuplicatedSubset S T → Fin 2
  | ⟨Sum.inl _⟩ => 0
  | ⟨Sum.inr _⟩ => 1

def duplicatedKey {n : ℕ} {S T : Finset (Fin n)}
    (x : DuplicatedSubset S T) : Fin n × Fin 2 :=
  (duplicatedValue x, duplicatedTag x)

lemma duplicatedKey_injective {n : ℕ} {S T : Finset (Fin n)} :
    Function.Injective (duplicatedKey (S := S) (T := T)) := by
  rintro ⟨x⟩ ⟨y⟩ h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          congr
          exact Subtype.ext (congrArg Prod.fst h)
      | inr y =>
          have htag := congrArg (fun q : Fin n × Fin 2 ↦ q.2.val) h
          simp [duplicatedKey, duplicatedTag] at htag
  | inr x =>
      cases y with
      | inl y =>
          have htag := congrArg (fun q : Fin n × Fin 2 ↦ q.2.val) h
          simp [duplicatedKey, duplicatedTag] at htag
      | inr y =>
          congr
          exact Subtype.ext (congrArg Prod.fst h)

instance duplicatedSubsetLinearOrder {n : ℕ} (S T : Finset (Fin n)) :
    LinearOrder (DuplicatedSubset S T) :=
  LinearOrder.lift' (fun x ↦ toLex (duplicatedKey x))
    (toLex.injective.comp duplicatedKey_injective)

lemma duplicated_lt_iff {n : ℕ} {S T : Finset (Fin n)}
    (x y : DuplicatedSubset S T) :
    x < y ↔ toLex (duplicatedKey x) < toLex (duplicatedKey y) := by
  rfl

lemma duplicated_le_iff {n : ℕ} {S T : Finset (Fin n)}
    (x y : DuplicatedSubset S T) :
    x ≤ y ↔ toLex (duplicatedKey x) ≤ toLex (duplicatedKey y) := by
  rfl

/-- Increasing enumeration of the tagged disjoint union. -/
def duplicatedOrderIso {n : ℕ} (S T : Finset (Fin n)) :
    Fin (S.card + T.card) ≃o DuplicatedSubset S T :=
  Fintype.orderIsoFinOfCardEq (DuplicatedSubset S T) (by
    calc
      Fintype.card (DuplicatedSubset S T) = Fintype.card (S ⊕ T) :=
        Fintype.card_congr (duplicatedEquivSum S T)
      _ = S.card + T.card := by simp)

/-- Position occupied by a member of the left subset. -/
def duplicatedLeftPosition {n : ℕ} (S T : Finset (Fin n)) :
    S ↪o Fin (S.card + T.card) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (duplicatedOrderIso S T).symm ⟨Sum.inl i⟩) <| by
      intro a b hab
      apply (duplicatedOrderIso S T).symm.strictMono
      rw [duplicated_lt_iff]
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hab

/-- Position occupied by a member of the right subset. -/
def duplicatedRightPosition {n : ℕ} (S T : Finset (Fin n)) :
    T ↪o Fin (S.card + T.card) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (duplicatedOrderIso S T).symm ⟨Sum.inr i⟩) <| by
      intro a b hab
      apply (duplicatedOrderIso S T).symm.strictMono
      rw [duplicated_lt_iff]
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hab

-- port to Lean 4.33.1: `unfold` of these now leaves an ill-typed `ofStrictMono` proof argument
lemma duplicatedLeftPosition_apply {n : ℕ} (S T : Finset (Fin n)) (i : S) :
    duplicatedLeftPosition S T i = (duplicatedOrderIso S T).symm ⟨Sum.inl i⟩ := rfl

lemma duplicatedRightPosition_apply {n : ℕ} (S T : Finset (Fin n)) (i : T) :
    duplicatedRightPosition S T i = (duplicatedOrderIso S T).symm ⟨Sum.inr i⟩ := rfl

/-- The positions of the left tagged copy. -/
def duplicatedLeftSet {n : ℕ} (S T : Finset (Fin n)) :
    Finset (Fin (S.card + T.card)) :=
  Finset.univ.map (duplicatedLeftPosition S T).toEmbedding

/-- The positions of the right tagged copy. -/
def duplicatedRightSet {n : ℕ} (S T : Finset (Fin n)) :
    Finset (Fin (S.card + T.card)) :=
  Finset.univ.map (duplicatedRightPosition S T).toEmbedding

@[simp] lemma card_duplicatedLeftSet {n : ℕ} (S T : Finset (Fin n)) :
    (duplicatedLeftSet S T).card = S.card := by
  simp [duplicatedLeftSet]

@[simp] lemma card_duplicatedRightSet {n : ℕ} (S T : Finset (Fin n)) :
    (duplicatedRightSet S T).card = T.card := by
  simp [duplicatedRightSet]

/-- Forget the tag at a position of the duplicated order. -/
def duplicatedForget {n : ℕ} (S T : Finset (Fin n))
    (i : Fin (S.card + T.card)) : Fin n :=
  duplicatedValue (duplicatedOrderIso S T i)

lemma duplicatedForget_mono {n : ℕ} (S T : Finset (Fin n)) :
    Monotone (duplicatedForget S T) := by
  intro i j hij
  have htagged := (duplicatedOrderIso S T).monotone hij
  rw [duplicated_le_iff] at htagged
  exact Prod.Lex.monotone_fst _ _ htagged

@[simp] lemma duplicatedForget_left {n : ℕ} (S T : Finset (Fin n)) (i : S) :
    duplicatedForget S T (duplicatedLeftPosition S T i) = i := by
  change duplicatedValue
      ((duplicatedOrderIso S T)
        ((duplicatedOrderIso S T).symm ⟨Sum.inl i⟩)) = i
  rw [OrderIso.apply_symm_apply]
  rfl

@[simp] lemma duplicatedForget_right {n : ℕ} (S T : Finset (Fin n)) (i : T) :
    duplicatedForget S T (duplicatedRightPosition S T i) = i := by
  change duplicatedValue
      ((duplicatedOrderIso S T)
        ((duplicatedOrderIso S T).symm ⟨Sum.inr i⟩)) = i
  rw [OrderIso.apply_symm_apply]
  rfl

/-- Positions strictly before the first tagged value which is at least `r`. -/
def duplicatedCutoff {n : ℕ} (S T : Finset (Fin n)) (r : Fin (n + 1)) :
    Fin (S.card + T.card + 1) :=
  ⟨(Finset.univ.filter fun i : Fin (S.card + T.card) ↦
      (duplicatedForget S T i).val < r.val).card,
    Nat.lt_succ_of_le (by
      calc
        (Finset.univ.filter fun i : Fin (S.card + T.card) ↦
            (duplicatedForget S T i).val < r.val).card
            ≤ (Finset.univ : Finset (Fin (S.card + T.card))).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
        _ = S.card + T.card := Finset.card_fin _)⟩

lemma lt_duplicatedCutoff_iff {n : ℕ} (S T : Finset (Fin n))
    (r : Fin (n + 1)) (i : Fin (S.card + T.card)) :
    i.val < (duplicatedCutoff S T r).val ↔
      (duplicatedForget S T i).val < r.val := by
  simpa [duplicatedCutoff] using
    (Fin.lt_card_filter_univ_iff_apply_of_imp
      (fun j : Fin (S.card + T.card) ↦
        (duplicatedForget S T j).val < r.val)
      (by
        intro a b hba ha
        exact lt_of_le_of_lt
          (Fin.mk_le_mk.mpr (duplicatedForget_mono S T hba)) ha)
      (j := i))

/-- Forget the tags of all positions in `P`. -/
def duplicatedImage {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card))) : Finset (Fin n) :=
  P.image (duplicatedForget S T)

lemma prefixCard_duplicatedImage {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card)))
    (hinj : Set.InjOn (duplicatedForget S T) P) (r : Fin (n + 1)) :
    prefixCard (duplicatedImage S T P) r =
      (P.filter fun i ↦ (duplicatedForget S T i).val < r.val).card := by
  unfold prefixCard duplicatedImage
  rw [Finset.filter_image, Finset.card_image_iff.mpr]
  exact Set.InjOn.mono (by
    intro i hi
    exact (Finset.mem_filter.mp
      (show i ∈ P.filter (fun j ↦ (duplicatedForget S T j).val < r.val)
        from hi)).1) hinj

lemma prefixCard_duplicatedCutoff {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card))) (r : Fin (n + 1)) :
    prefixCard P (duplicatedCutoff S T r) =
      (P.filter fun i ↦ (duplicatedForget S T i).val < r.val).card := by
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter]
  rw [lt_duplicatedCutoff_iff]

lemma duplicatedImage_leftSet {n : ℕ} (S T : Finset (Fin n)) :
    duplicatedImage S T (duplicatedLeftSet S T) = S := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    rcases Finset.mem_map.mp hp with ⟨j, -, rfl⟩
    change duplicatedForget S T (duplicatedLeftPosition S T j) = i at hpi
    rw [duplicatedForget_left] at hpi
    rw [← hpi]
    exact j.property
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨duplicatedLeftPosition S T ⟨i, hi⟩, ?_, ?_⟩
    · simp [duplicatedLeftSet]
    · simp

lemma duplicatedImage_rightSet {n : ℕ} (S T : Finset (Fin n)) :
    duplicatedImage S T (duplicatedRightSet S T) = T := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    rcases Finset.mem_map.mp hp with ⟨j, -, rfl⟩
    change duplicatedForget S T (duplicatedRightPosition S T j) = i at hpi
    rw [duplicatedForget_right] at hpi
    rw [← hpi]
    exact j.property
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨duplicatedRightPosition S T ⟨i, hi⟩, ?_, ?_⟩
    · simp [duplicatedRightSet]
    · simp

lemma duplicatedForget_injOn_leftSet {n : ℕ} (S T : Finset (Fin n)) :
    Set.InjOn (duplicatedForget S T) (duplicatedLeftSet S T) := by
  intro p hp q hq hpq
  rcases Finset.mem_map.mp hp with ⟨i, -, rfl⟩
  rcases Finset.mem_map.mp hq with ⟨j, -, rfl⟩
  change duplicatedForget S T (duplicatedLeftPosition S T i) =
    duplicatedForget S T (duplicatedLeftPosition S T j) at hpq
  rw [duplicatedForget_left, duplicatedForget_left] at hpq
  exact congrArg (duplicatedLeftPosition S T) (Subtype.ext hpq)

lemma duplicatedForget_injOn_rightSet {n : ℕ} (S T : Finset (Fin n)) :
    Set.InjOn (duplicatedForget S T) (duplicatedRightSet S T) := by
  intro p hp q hq hpq
  rcases Finset.mem_map.mp hp with ⟨i, -, rfl⟩
  rcases Finset.mem_map.mp hq with ⟨j, -, rfl⟩
  change duplicatedForget S T (duplicatedRightPosition S T i) =
    duplicatedForget S T (duplicatedRightPosition S T j) at hpq
  rw [duplicatedForget_right, duplicatedForget_right] at hpq
  exact congrArg (duplicatedRightPosition S T) (Subtype.ext hpq)

lemma duplicatedLeftPosition_ne_rightPosition {n : ℕ}
    (S T : Finset (Fin n)) (i : S) (j : T) :
    duplicatedLeftPosition S T i ≠ duplicatedRightPosition S T j := by
  intro hij
  have htag := congrArg (duplicatedOrderIso S T) hij
  simp only [duplicatedLeftPosition_apply, duplicatedRightPosition_apply, OrderIso.apply_symm_apply] at htag
  cases congrArg DuplicatedSubset.toSum htag

lemma duplicatedLeftSet_compl {n : ℕ} (S T : Finset (Fin n)) :
    (duplicatedLeftSet S T)ᶜ = duplicatedRightSet S T := by
  ext p
  let x := duplicatedOrderIso S T p
  have hp : (duplicatedOrderIso S T).symm x = p :=
    (duplicatedOrderIso S T).symm_apply_apply p
  rcases x with ⟨i | j⟩
  · have hpleft : duplicatedLeftPosition S T i = p := by
      rw [duplicatedLeftPosition_apply]
      exact hp
    subst p
    constructor
    · intro hcomp
      apply (Finset.mem_compl.mp hcomp).elim
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, hpleft⟩
    · intro hright
      rcases Finset.mem_map.mp hright with ⟨j, -, hj⟩
      exact (duplicatedLeftPosition_ne_rightPosition S T i j
        (hpleft.trans hj.symm)).elim
  · have hpright : duplicatedRightPosition S T j = p := by
      rw [duplicatedRightPosition_apply]
      exact hp
    subst p
    constructor
    · intro _
      exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, hpright⟩
    · intro _
      apply Finset.mem_compl.mpr
      intro hleft
      rcases Finset.mem_map.mp hleft with ⟨i, -, hi⟩
      exact duplicatedLeftPosition_ne_rightPosition S T i j
        (hi.trans hpright.symm)

lemma prefixCard_leftSet_cutoff {n : ℕ} (S T : Finset (Fin n))
    (r : Fin (n + 1)) :
    prefixCard (duplicatedLeftSet S T) (duplicatedCutoff S T r) =
      prefixCard S r := by
  rw [prefixCard_duplicatedCutoff]
  rw [← prefixCard_duplicatedImage S T (duplicatedLeftSet S T)
    (duplicatedForget_injOn_leftSet S T) r]
  rw [duplicatedImage_leftSet]

lemma duplicatedImage_prefixLE {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card)))
    (hinj : Set.InjOn (duplicatedForget S T) P)
    (hP : P ≼ₚ duplicatedLeftSet S T) :
    duplicatedImage S T P ≼ₚ S := by
  intro r
  calc
    prefixCard S r =
        prefixCard (duplicatedLeftSet S T) (duplicatedCutoff S T r) :=
      (prefixCard_leftSet_cutoff S T r).symm
    _ ≤ prefixCard P (duplicatedCutoff S T r) :=
      hP (duplicatedCutoff S T r)
    _ = (P.filter fun i ↦ (duplicatedForget S T i).val < r.val).card :=
      prefixCard_duplicatedCutoff S T P r
    _ = prefixCard (duplicatedImage S T P) r :=
      (prefixCard_duplicatedImage S T P hinj r).symm

lemma duplicatedImage_prefixLE_of_prefixLE {n : ℕ}
    (S T : Finset (Fin n))
    (P Q : Finset (Fin (S.card + T.card)))
    (hinjP : Set.InjOn (duplicatedForget S T) P)
    (hinjQ : Set.InjOn (duplicatedForget S T) Q)
    (hPQ : P ≼ₚ Q) :
    duplicatedImage S T P ≼ₚ duplicatedImage S T Q := by
  intro r
  calc
    prefixCard (duplicatedImage S T Q) r =
        (Q.filter fun i ↦ (duplicatedForget S T i).val < r.val).card :=
      prefixCard_duplicatedImage S T Q hinjQ r
    _ = prefixCard Q (duplicatedCutoff S T r) :=
      (prefixCard_duplicatedCutoff S T Q r).symm
    _ ≤ prefixCard P (duplicatedCutoff S T r) :=
      hPQ (duplicatedCutoff S T r)
    _ = (P.filter fun i ↦ (duplicatedForget S T i).val < r.val).card :=
      prefixCard_duplicatedCutoff S T P r
    _ = prefixCard (duplicatedImage S T P) r :=
      (prefixCard_duplicatedImage S T P hinjP r).symm

lemma duplicatedLeftPosition_le_of_forget_mem {n : ℕ}
    (S T : Finset (Fin n)) (p : Fin (S.card + T.card))
    (hp : duplicatedForget S T p ∈ S) :
    duplicatedLeftPosition S T ⟨duplicatedForget S T p, hp⟩ ≤ p := by
  rw [duplicatedLeftPosition_apply]
  have htagged :
      (⟨Sum.inl ⟨duplicatedForget S T p, hp⟩⟩ : DuplicatedSubset S T) ≤
        duplicatedOrderIso S T p := by
    rw [duplicated_le_iff]
    rw [Prod.Lex.toLex_le_toLex]
    refine Or.inr ⟨rfl, ?_⟩
    exact Fin.zero_le _
  have h := (duplicatedOrderIso S T).symm.monotone htagged
  simpa only [OrderIso.symm_apply_apply] using h

/-- If an injective choice of tags forgets to exactly `S`, choosing left tags
instead can only move its positions earlier. -/
lemma duplicatedLeftSet_prefixLE_of_image_eq {n : ℕ}
    (S T : Finset (Fin n)) (P : Finset (Fin (S.card + T.card)))
    (hinj : Set.InjOn (duplicatedForget S T) P)
    (himage : duplicatedImage S T P = S) :
    duplicatedLeftSet S T ≼ₚ P := by
  have forget_mem (p : Fin (S.card + T.card)) (hp : p ∈ P) :
      duplicatedForget S T p ∈ S := by
    have hmem : duplicatedForget S T p ∈ duplicatedImage S T P :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    simpa only [himage] using hmem
  intro r
  let source := P.filter fun p ↦ p.val < r.val
  let target := (duplicatedLeftSet S T).filter fun p ↦ p.val < r.val
  let f : source → target := fun p ↦
    ⟨duplicatedLeftPosition S T
        ⟨duplicatedForget S T p,
          forget_mem p (Finset.mem_filter.mp p.property).1⟩,
      Finset.mem_filter.mpr ⟨by
        simp [duplicatedLeftSet], by
        exact lt_of_le_of_lt
          (duplicatedLeftPosition_le_of_forget_mem S T p
            (forget_mem p (Finset.mem_filter.mp p.property).1))
          (Finset.mem_filter.mp p.property).2⟩⟩
  exact Finset.card_le_card_of_injective (f := f) (by
    intro p q hpq
    apply Subtype.ext
    apply hinj
    · exact (Finset.mem_filter.mp p.property).1
    · exact (Finset.mem_filter.mp q.property).1
    · have hpos := congrArg Subtype.val hpq
      change duplicatedLeftPosition S T
          ⟨duplicatedForget S T p,
            forget_mem p (Finset.mem_filter.mp p.property).1⟩ =
        duplicatedLeftPosition S T
          ⟨duplicatedForget S T q,
            forget_mem q (Finset.mem_filter.mp q.property).1⟩ at hpos
      have hsub := (duplicatedLeftPosition S T).injective hpos
      exact congrArg Subtype.val hsub)

/-- Strict prefix descent survives forgetting tags, provided no underlying
value is repeated on the chosen subset. -/
lemma duplicatedImage_prefixLT {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card)))
    (hinj : Set.InjOn (duplicatedForget S T) P)
    (hP : P ≺ₚ duplicatedLeftSet S T) :
    duplicatedImage S T P ≺ₚ S := by
  refine ⟨duplicatedImage_prefixLE S T P hinj hP.1, ?_⟩
  intro himage
  apply hP.2
  exact prefixLE_antisymm hP.1
    (duplicatedLeftSet_prefixLE_of_image_eq S T P hinj himage)

end GenericMaximalMinor

end
end
end

section
section
/-!
# Straightening two minors of a rectangular generic matrix

This file transports the square Laplace straightening theorem through the
tagged row and column orders.  The first layer below packages a minor by its
two finite index sets; this is the paper-facing representation used by the
straightening statement.
-/

noncomputable section

namespace GenericMaximalMinor

/-- The canonical minor index associated to equally large row and column
sets.  Both sets are enumerated in increasing order. -/
def minorIndexOfFinsets {n m : ℕ} (A : Finset (Fin n)) (B : Finset (Fin m))
    (hcard : A.card = B.card) : MinorIndex n m where
  size := ⟨A.card, by
    have hAn : A.card ≤ n := by
      simpa using Finset.card_le_univ A
    have hBm : B.card ≤ m := by
      simpa using Finset.card_le_univ B
    omega⟩
  rows := A.orderEmbOfFin rfl
  cols := B.orderEmbOfFin hcard.symm

@[simp] lemma rowSet_minorIndexOfFinsets {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card = B.card) :
    (minorIndexOfFinsets A B hcard).rowSet = A := by
  exact Finset.map_orderEmbOfFin_univ A rfl

@[simp] lemma colSet_minorIndexOfFinsets {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card = B.card) :
    (minorIndexOfFinsets A B hcard).colSet = B := by
  exact Finset.map_orderEmbOfFin_univ B hcard.symm

/-- The canonical generic minor selected by two finite subsets.  As with
`finsetMinor`, unequal cardinalities give zero. -/
def finsetMinorPoly {D : Type*} [CommRing D] {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) : GenericPoly D n m :=
  if h : A.card = B.card then minorPoly (minorIndexOfFinsets A B h) else 0

@[simp] lemma finsetMinorPoly_of_card_ne {D : Type*} [CommRing D] {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card ≠ B.card) :
    finsetMinorPoly (D := D) A B = 0 := by
  simp [finsetMinorPoly, hcard]

lemma finsetMinorPoly_of_card_eq {D : Type*} [CommRing D] {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card = B.card) :
    finsetMinorPoly (D := D) A B = minorPoly (minorIndexOfFinsets A B hcard) := by
  rw [finsetMinorPoly, dif_pos hcard]

/-! ## Transporting subsets across equal finite cardinalities -/

/-- Transport a subset of `Fin a` across an equality `a = b`. -/
def castFinset {a b : ℕ} (h : a = b) (P : Finset (Fin a)) : Finset (Fin b) :=
  P.map (Fin.castOrderIso h).toEmbedding

@[simp] lemma card_castFinset {a b : ℕ} (h : a = b) (P : Finset (Fin a)) :
    (castFinset h P).card = P.card := by
  simp [castFinset]

@[simp] lemma mem_castFinset_iff {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) (i : Fin b) :
    i ∈ castFinset h P ↔ (Fin.castOrderIso h).symm i ∈ P := by
  simp [castFinset]

@[simp] lemma castFinset_univ {a b : ℕ} (h : a = b) :
    castFinset h (Finset.univ : Finset (Fin a)) = Finset.univ := by
  ext i
  simp

@[simp] lemma castFinset_compl {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) :
    castFinset h Pᶜ = (castFinset h P)ᶜ := by
  ext i
  simp

lemma prefixLE_castFinset_iff {a b : ℕ} (h : a = b)
    (P Q : Finset (Fin a)) :
    castFinset h P ≼ₚ castFinset h Q ↔ P ≼ₚ Q := by
  subst b
  simpa [castFinset] using (Iff.rfl : P ≼ₚ Q ↔ P ≼ₚ Q)

lemma prefixLT_castFinset_iff {a b : ℕ} (h : a = b)
    (P Q : Finset (Fin a)) :
    castFinset h P ≺ₚ castFinset h Q ↔ P ≺ₚ Q := by
  subst b
  simpa [castFinset] using (Iff.rfl : P ≺ₚ Q ↔ P ≺ₚ Q)

@[simp] lemma castFinset_symm_castFinset {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) :
    castFinset h.symm (castFinset h P) = P := by
  subst b
  simp [castFinset]

@[simp] lemma castFinset_castFinset_symm {a b : ℕ} (h : a = b)
    (P : Finset (Fin b)) :
    castFinset h (castFinset h.symm P) = P := by
  subst b
  simp [castFinset]

/-- Transport the domain of a function between equal finite types. -/
def castFinFunction {a b : ℕ} (h : a = b) {γ : Type*}
    (f : Fin a → γ) : Fin b → γ :=
  fun i ↦ f ((Fin.castOrderIso h).symm i)

/-- Pull a subset back along the same finite cast equivalence. -/
def castFinsetBack {a b : ℕ} (h : a = b)
    (P : Finset (Fin b)) : Finset (Fin a) :=
  P.map (Fin.castOrderIso h).symm.toEmbedding

@[simp] lemma castFinset_castFinsetBack {a b : ℕ} (h : a = b)
    (P : Finset (Fin b)) :
    castFinset h (castFinsetBack h P) = P := by
  ext i
  simp [castFinset, castFinsetBack]

@[simp] lemma castFinsetBack_castFinset {a b : ℕ} (h : a = b)
    (P : Finset (Fin a)) :
    castFinsetBack h (castFinset h P) = P := by
  ext i
  simp [castFinset, castFinsetBack]

lemma injOn_castFinFunction_iff {a b : ℕ} (h : a = b) {γ : Type*}
    (f : Fin a → γ) (P : Finset (Fin b)) :
    Set.InjOn (castFinFunction h f) P ↔
      Set.InjOn f (castFinsetBack h P) := by
  let e : Fin a ≃o Fin b := Fin.castOrderIso h
  constructor
  · intro hinj x hx y hy hxy
    have hex : e x ∈ P := by
      simpa [castFinsetBack, e] using hx
    have hey : e y ∈ P := by
      simpa [castFinsetBack, e] using hy
    apply e.injective
    apply hinj hex hey
    simpa [castFinFunction, e] using hxy
  · intro hinj x hx y hy hxy
    apply e.symm.injective
    apply hinj
    · exact Finset.mem_map.mpr ⟨x, hx, by simp [e]⟩
    · exact Finset.mem_map.mpr ⟨y, hy, by simp [e]⟩
    · simpa [castFinFunction, e] using hxy

@[simp] lemma image_castFinFunction {a b : ℕ} (h : a = b) {γ : Type*}
    [DecidableEq γ] (f : Fin a → γ) (P : Finset (Fin b)) :
    P.image (castFinFunction h f) = (castFinsetBack h P).image f := by
  rw [castFinsetBack, Finset.map_eq_image, Finset.image_image]
  rfl

lemma castFinFunction_mono {a b : ℕ} (h : a = b)
    {γ : Type*} [Preorder γ] (f : Fin a → γ) (hf : Monotone f) :
    Monotone (castFinFunction h f) := by
  intro i j hij
  exact hf ((Fin.castOrderIso h).symm.monotone hij)

/-! ## The duplicated square matrix attached to two rectangular minors -/

/-- Column positions transported to the cardinality of the duplicated row
order. -/
def rectangularColLeftSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Finset (Fin (S₁.card + S₂.card)) :=
  castFinset hsize (duplicatedLeftSet T₁ T₂)

/-- Forget a transported column tag. -/
def rectangularColForget {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Fin (S₁.card + S₂.card) → Fin m :=
  castFinFunction hsize (duplicatedForget T₁ T₂)

/-- The square generic matrix obtained by duplicating the row and column
content of two rectangular minors. -/
def rectangularDuplicatedMatrix {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Matrix (Fin (S₁.card + S₂.card)) (Fin (S₁.card + S₂.card))
      (GenericPoly D n m) :=
  fun i j ↦ MvPolynomial.X
    (duplicatedForget S₁ S₂ i,
      rectangularColForget S₁ S₂ T₁ T₂ hsize j)

@[simp] lemma rectangularColLeftSet_compl {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)ᶜ =
      castFinset hsize (duplicatedRightSet T₁ T₂) := by
  rw [rectangularColLeftSet, ← castFinset_compl, duplicatedLeftSet_compl]

lemma rectangularColImage_prefixLT {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (P : Finset (Fin (S₁.card + S₂.card)))
    (hinj : Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize) P)
    (hP : P ≺ₚ rectangularColLeftSet S₁ S₂ T₁ T₂ hsize) :
    P.image (rectangularColForget S₁ S₂ T₁ T₂ hsize) ≺ₚ T₁ := by
  have hinj' : Set.InjOn (duplicatedForget T₁ T₂)
      (castFinsetBack hsize P) :=
    (injOn_castFinFunction_iff hsize (duplicatedForget T₁ T₂) P).mp hinj
  have hP' : castFinsetBack hsize P ≺ₚ duplicatedLeftSet T₁ T₂ := by
    have hcast := (prefixLT_castFinset_iff hsize
      (castFinsetBack hsize P) (duplicatedLeftSet T₁ T₂)).mp
    exact hcast (by
      simpa [rectangularColLeftSet] using hP)
  have hstrict := duplicatedImage_prefixLT T₁ T₂
    (castFinsetBack hsize P) hinj' hP'
  simpa [duplicatedImage, rectangularColForget] using hstrict

lemma rectangularColImage_prefixLE_of_prefixLE {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (P Q : Finset (Fin (S₁.card + S₂.card)))
    (hinjP : Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize) P)
    (hinjQ : Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize) Q)
    (hPQ : P ≼ₚ Q) :
    P.image (rectangularColForget S₁ S₂ T₁ T₂ hsize) ≼ₚ
      Q.image (rectangularColForget S₁ S₂ T₁ T₂ hsize) := by
  have hinjP' : Set.InjOn (duplicatedForget T₁ T₂)
      (castFinsetBack hsize P) :=
    (injOn_castFinFunction_iff hsize (duplicatedForget T₁ T₂) P).mp hinjP
  have hinjQ' : Set.InjOn (duplicatedForget T₁ T₂)
      (castFinsetBack hsize Q) :=
    (injOn_castFinFunction_iff hsize (duplicatedForget T₁ T₂) Q).mp hinjQ
  have hPQ' : castFinsetBack hsize P ≼ₚ castFinsetBack hsize Q := by
    apply (prefixLE_castFinset_iff hsize _ _).mp
    simpa using hPQ
  have hle := duplicatedImage_prefixLE_of_prefixLE T₁ T₂
    (castFinsetBack hsize P) (castFinsetBack hsize Q) hinjP' hinjQ' hPQ'
  simpa [duplicatedImage, rectangularColForget] using hle

/-! ## Identifying surviving duplicated minors -/

/-- Pulling the generic matrix back along two monotone maps does not change a
minor when both maps are injective on the selected positions.  The increasing
enumerations on both sides agree, so no sign is introduced here. -/
lemma finsetMinor_pulledGenericMatrix {D : Type*} [CommRing D]
    {N n m : ℕ} (f : Fin N → Fin n) (g : Fin N → Fin m)
    (hf : Monotone f) (hg : Monotone g)
    (P Q : Finset (Fin N))
    (hinjP : Set.InjOn f P) (hinjQ : Set.InjOn g Q) :
    finsetMinor (Matrix.of fun i j ↦ (MvPolynomial.X (f i, g j) : GenericPoly D n m)) P Q =
      finsetMinorPoly (D := D) (P.image f) (Q.image g) := by
  classical
  by_cases hPQ : P.card = Q.card
  · have hA : (P.image f).card = P.card :=
      Finset.card_image_iff.mpr hinjP
    have hB : (Q.image g).card = Q.card :=
      Finset.card_image_iff.mpr hinjQ
    have hAB : (P.image f).card = (Q.image g).card :=
      hA.trans (hPQ.trans hB.symm)
    letI : Fintype P := Subtype.fintype (fun i : Fin N ↦ i ∈ P)
    rw [finsetMinor, dif_pos hPQ, finsetMinorPoly, dif_pos hAB]
    let eP : Fin (P.image f).card ≃o P :=
      (Fin.castOrderIso hA).trans (P.orderIsoOfFin rfl)
    let ePQ : P ≃o Q :=
      (P.orderIsoOfFin rfl).symm.trans (Q.orderIsoOfFin hPQ.symm)
    have hePQ : ePQ.toEquiv = orderedFinsetEquiv P Q hPQ := by
      rfl
    have hrowStrict : StrictMono (fun i ↦ f (eP i)) := by
      intro i j hij
      have hij' : eP i < eP j := eP.strictMono hij
      have hle : f (eP i) ≤ f (eP j) := hf hij'.le
      exact lt_of_le_of_ne hle (by
        intro heq
        apply hij'.ne
        apply Subtype.ext
        exact hinjP (eP i).property (eP j).property heq)
    have hcolStrict : StrictMono (fun i ↦ g (ePQ (eP i))) := by
      intro i j hij
      have hij' : ePQ (eP i) < ePQ (eP j) :=
        ePQ.strictMono (eP.strictMono hij)
      have hle : g (ePQ (eP i)) ≤ g (ePQ (eP j)) := hg hij'.le
      exact lt_of_le_of_ne hle (by
        intro heq
        apply hij'.ne
        apply Subtype.ext
        exact hinjQ (ePQ (eP i)).property (ePQ (eP j)).property heq)
    have hrowEnum :
        (fun i ↦ f (eP i)) = (P.image f).orderEmbOfFin rfl := by
      apply Finset.orderEmbOfFin_unique rfl
      · intro i
        exact Finset.mem_image.mpr ⟨eP i, (eP i).property, rfl⟩
      · exact hrowStrict
    have hcolEnum :
        (fun i ↦ g (ePQ (eP i))) =
          (Q.image g).orderEmbOfFin hAB.symm := by
      apply Finset.orderEmbOfFin_unique hAB.symm
      · intro i
        exact Finset.mem_image.mpr
          ⟨ePQ (eP i), (ePQ (eP i)).property, rfl⟩
      · exact hcolStrict
    let M : Matrix P P (GenericPoly D n m) :=
      fun i j ↦ MvPolynomial.X
        (f i, g (orderedFinsetEquiv P Q hPQ j))
    unfold minorAlongEquiv
    change Matrix.det M = minorPoly (minorIndexOfFinsets
      (P.image f) (Q.image g) hAB)
    unfold minorPoly minorMatrix
    calc
      Matrix.det M = Matrix.det (M.reindex eP.symm.toEquiv eP.symm.toEquiv) :=
        (Matrix.det_reindex_self eP.symm.toEquiv M).symm
      _ = Matrix.det (fun i j ↦
          MvPolynomial.X
            ((minorIndexOfFinsets (P.image f) (Q.image g) hAB).rows i,
              (minorIndexOfFinsets (P.image f) (Q.image g) hAB).cols j)) := by
        apply congrArg Matrix.det
        funext i j
        change MvPolynomial.X
            (f (eP i), g (orderedFinsetEquiv P Q hPQ (eP j))) =
          MvPolynomial.X
            ((minorIndexOfFinsets (P.image f) (Q.image g) hAB).rows i,
              (minorIndexOfFinsets (P.image f) (Q.image g) hAB).cols j)
        rw [← hePQ]
        change MvPolynomial.X (f (eP i), g (ePQ (eP j))) =
          MvPolynomial.X
            ((P.image f).orderEmbOfFin rfl i,
              (Q.image g).orderEmbOfFin hAB.symm j)
        rw [← congrFun hrowEnum i, ← congrFun hcolEnum j]
  · rw [finsetMinor_of_card_ne _ _ _ hPQ]
    apply (finsetMinorPoly_of_card_ne (D := D) (P.image f) (Q.image g) ?_).symm
    intro himage
    apply hPQ
    have hA : (P.image f).card = P.card :=
      Finset.card_image_iff.mpr hinjP
    have hB : (Q.image g).card = Q.card :=
      Finset.card_image_iff.mpr hinjQ
    omega

lemma finsetMinor_pulled_eq_zero_of_not_injOn_left
    {R : Type*} [CommRing R] {N n m : ℕ}
    (H : Fin n → Fin m → R) (f : Fin N → Fin n) (g : Fin N → Fin m)
    (P Q : Finset (Fin N)) (hnot : ¬Set.InjOn f P) :
    finsetMinor (Matrix.of fun i j ↦ H (f i) (g j)) P Q = 0 := by
  classical
  by_cases hcard : P.card = Q.card
  · letI : Fintype P := Subtype.fintype (fun i : Fin N ↦ i ∈ P)
    unfold Set.InjOn at hnot
    push Not at hnot
    rcases hnot with ⟨x, hx, y, hy, hxy, hne⟩
    rw [finsetMinor, dif_pos hcard]
    unfold minorAlongEquiv
    apply Matrix.det_zero_of_row_eq
      (show (⟨x, hx⟩ : P) ≠ ⟨y, hy⟩ by
        intro heq
        exact hne (congrArg Subtype.val heq))
    funext j
    change H (f x) _ = H (f y) _
    rw [hxy]
  · exact finsetMinor_of_card_ne _ _ _ hcard

lemma finsetMinor_pulled_eq_zero_of_not_injOn_right
    {R : Type*} [CommRing R] {N n m : ℕ}
    (H : Fin n → Fin m → R) (f : Fin N → Fin n) (g : Fin N → Fin m)
    (P Q : Finset (Fin N)) (hnot : ¬Set.InjOn g Q) :
    finsetMinor (Matrix.of fun i j ↦ H (f i) (g j)) P Q = 0 := by
  classical
  by_cases hcard : P.card = Q.card
  · letI : Fintype P := Subtype.fintype (fun i : Fin N ↦ i ∈ P)
    unfold Set.InjOn at hnot
    push Not at hnot
    rcases hnot with ⟨x, hx, y, hy, hxy, hne⟩
    let e : P ≃ Q := orderedFinsetEquiv P Q hcard
    let i : P := e.symm ⟨x, hx⟩
    let j : P := e.symm ⟨y, hy⟩
    have hij : i ≠ j := by
      intro hij
      apply hne
      have := congrArg (fun q : P ↦ (e q : Fin N)) hij
      simpa [i, j, e] using this
    rw [finsetMinor, dif_pos hcard]
    unfold minorAlongEquiv
    apply Matrix.det_zero_of_column_eq hij
    intro k
    change H _ (g (e i)) = H _ (g (e j))
    rw [show e i = (⟨x, hx⟩ : Q) by simp [i],
      show e j = (⟨y, hy⟩ : Q) by simp [j], hxy]
  · exact finsetMinor_of_card_ne _ _ _ hcard

lemma finsetMinor_rectangularDuplicatedMatrix {D : Type*} [CommRing D]
    {n m : ℕ} (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (P Q : Finset (Fin (S₁.card + S₂.card)))
    (hinjP : Set.InjOn (duplicatedForget S₁ S₂) P)
    (hinjQ : Set.InjOn
      (rectangularColForget S₁ S₂ T₁ T₂ hsize) Q) :
    finsetMinor (rectangularDuplicatedMatrix (D := D)
        S₁ S₂ T₁ T₂ hsize) P Q =
      finsetMinorPoly (D := D)
        (P.image (duplicatedForget S₁ S₂))
        (Q.image (rectangularColForget S₁ S₂ T₁ T₂ hsize)) := by
  exact finsetMinor_pulledGenericMatrix
    (duplicatedForget S₁ S₂)
    (rectangularColForget S₁ S₂ T₁ T₂ hsize)
    (duplicatedForget_mono S₁ S₂)
    (castFinFunction_mono hsize (duplicatedForget T₁ T₂)
      (duplicatedForget_mono T₁ T₂))
    P Q hinjP hinjQ

lemma rectangularColForget_injOn_leftSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize)
      (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize) := by
  unfold rectangularColForget rectangularColLeftSet
  rw [injOn_castFinFunction_iff]
  simpa using
    (duplicatedForget_injOn_leftSet T₁ T₂)

lemma rectangularColForget_injOn_rightSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    Set.InjOn (rectangularColForget S₁ S₂ T₁ T₂ hsize)
      (castFinset hsize (duplicatedRightSet T₁ T₂)) := by
  unfold rectangularColForget
  rw [injOn_castFinFunction_iff]
  simpa using (duplicatedForget_injOn_rightSet T₁ T₂)

@[simp] lemma rectangularColImage_leftSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize).image
        (rectangularColForget S₁ S₂ T₁ T₂ hsize) = T₁ := by
  unfold rectangularColForget rectangularColLeftSet
  rw [image_castFinFunction]
  simpa [duplicatedImage] using
    (duplicatedImage_leftSet T₁ T₂)

@[simp] lemma rectangularColImage_rightSet {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    (castFinset hsize (duplicatedRightSet T₁ T₂)).image
        (rectangularColForget S₁ S₂ T₁ T₂ hsize) = T₂ := by
  unfold rectangularColForget
  rw [image_castFinFunction]
  simpa [duplicatedImage] using (duplicatedImage_rightSet T₁ T₂)

lemma finsetMinor_rectangularDuplicatedMatrix_left {D : Type*} [CommRing D]
    {n m : ℕ} (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    finsetMinor (rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize)
        (duplicatedLeftSet S₁ S₂)
        (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize) =
      finsetMinorPoly (D := D) S₁ T₁ := by
  rw [finsetMinor_rectangularDuplicatedMatrix
    S₁ S₂ T₁ T₂ hsize
    (duplicatedLeftSet S₁ S₂)
    (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)
    (duplicatedForget_injOn_leftSet S₁ S₂)
    (rectangularColForget_injOn_leftSet S₁ S₂ T₁ T₂ hsize)]
  rw [← duplicatedImage]
  rw [duplicatedImage_leftSet, rectangularColImage_leftSet]

lemma finsetMinor_rectangularDuplicatedMatrix_right {D : Type*} [CommRing D]
    {n m : ℕ} (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card) :
    finsetMinor (rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize)
        (duplicatedRightSet S₁ S₂)
        (castFinset hsize (duplicatedRightSet T₁ T₂)) =
      finsetMinorPoly (D := D) S₂ T₂ := by
  rw [finsetMinor_rectangularDuplicatedMatrix
    S₁ S₂ T₁ T₂ hsize
    (duplicatedRightSet S₁ S₂)
    (castFinset hsize (duplicatedRightSet T₁ T₂))
    (duplicatedForget_injOn_rightSet S₁ S₂)
    (rectangularColForget_injOn_rightSet S₁ S₂ T₁ T₂ hsize)]
  rw [← duplicatedImage]
  rw [duplicatedImage_rightSet, rectangularColImage_rightSet]

/-! ## Signed Laplace products -/

lemma intUnit_cast_mul_mem_iff {R : Type*} [CommRing R]
    (H : AddSubgroup R) (u : ℤˣ) (x : R) :
    (u : R) * x ∈ H ↔ x ∈ H := by
  have hu : u = 1 ∨ u = -1 := by
    have hmem : u ∈ (Finset.univ : Finset ℤˣ) := Finset.mem_univ u
    rw [UnitsInt.univ] at hmem
    simpa using hmem
  rcases hu with rfl | rfl
  · simp
  · simpa using H.neg_mem_iff

/-- A signed Laplace permutation sum is the product of its two complementary
canonical minors.  The single coefficient is an integer unit, hence only a
harmless sign over every coefficient ring. -/
lemma exists_intUnit_mul_laplacePermSum_eq_mul_finsetMinor
    {R : Type*} [CommRing R] {N : ℕ}
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card = B.card) :
    ∃ u : ℤˣ, (u : R) * laplacePermSum Y A B =
      finsetMinor Y A B * finsetMinor Y Aᶜ Bᶜ := by
  classical
  let e : A ≃ B := orderedFinsetEquiv A B hcard
  have hcomp : Aᶜ.card = Bᶜ.card := by
    simpa [Finset.card_compl] using congrArg (fun k ↦ N - k) hcard
  letI : Fintype {i : Fin N // i ∈ Aᶜ} :=
    Subtype.fintype (fun i : Fin N ↦ i ∈ Aᶜ)
  letI : Fintype {i : Fin N // ¬i ∈ A} :=
    Subtype.fintype (fun i : Fin N ↦ ¬i ∈ A)
  let cA : {i : Fin N // i ∈ Aᶜ} ≃ {i : Fin N // ¬i ∈ A} :=
    Equiv.subtypeEquivRight (fun i ↦ by simp)
  let cB : {i : Fin N // i ∈ Bᶜ} ≃ {i : Fin N // ¬i ∈ B} :=
    Equiv.subtypeEquivRight (fun i ↦ by simp)
  let ec : {i : Fin N // i ∈ Aᶜ} ≃ {i : Fin N // i ∈ Bᶜ} :=
    cA.trans (e.toCompl.trans cB.symm)
  let s₁ : ℤˣ := Equiv.Perm.sign e.extendSubtype
  let s₂ : ℤˣ := Equiv.Perm.sign
    (ec.trans (orderedFinsetEquiv Aᶜ Bᶜ hcomp).symm)
  have hleft : minorAlongEquiv Y e = finsetMinor Y A B := by
    rw [finsetMinor, dif_pos hcard]
  have hcompMinor : minorAlongEquiv Y e.toCompl = minorAlongEquiv Y ec := by
    let M : Matrix {i : Fin N // ¬i ∈ A} {i : Fin N // ¬i ∈ A} R :=
      fun i j ↦ Y i (e.toCompl j)
    let Mc : Matrix {i : Fin N // i ∈ Aᶜ} {i : Fin N // i ∈ Aᶜ} R :=
      fun i j ↦ Y i (ec j)
    unfold minorAlongEquiv
    change Matrix.det M = Matrix.det Mc
    calc
      Matrix.det M = Matrix.det (M.reindex cA.symm cA.symm) :=
        (Matrix.det_reindex_self cA.symm M).symm
      _ = Matrix.det Mc := by
        apply congrArg Matrix.det
        funext i j
        rfl
  have hright : minorAlongEquiv Y e.toCompl =
      (s₂ : R) * finsetMinor Y Aᶜ Bᶜ := by
    rw [hcompMinor]
    simpa [s₂] using
      (minorAlongEquiv_eq_sign_mul_finsetMinor Y Aᶜ Bᶜ hcomp ec)
  have hblock := sign_mul_det_maskedMatrix_eq_mul_minors Y A B e
  rw [← laplacePermSum_eq_det_maskedMatrix, hleft, hright] at hblock
  refine ⟨s₂ * s₁, ?_⟩
  simp only [Units.val_mul, Int.cast_mul]
  calc
    (s₂ : R) * (s₁ : R) * laplacePermSum Y A B =
        (s₂ : R) * ((s₁ : R) * laplacePermSum Y A B) := by ring
    _ = (s₂ : R) * ((s₂ : R) *
        (finsetMinor Y A B * finsetMinor Y Aᶜ Bᶜ)) := by
      rw [hblock]
      ring
    _ = finsetMinor Y A B * finsetMinor Y Aᶜ Bᶜ := by
      rw [← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self]
      simp

/-! ## The rectangular straightening span -/

lemma row_left_prefixLE_right_of_good {n : ℕ}
    (S₁ S₂ : Finset (Fin n)) (hgood : GoodSubset (duplicatedLeftSet S₁ S₂)) :
    S₁ ≼ₚ S₂ := by
  have hpos : duplicatedLeftSet S₁ S₂ ≼ₚ duplicatedRightSet S₁ S₂ := by
    rw [← duplicatedLeftSet_compl]
    exact hgood
  have himage := duplicatedImage_prefixLE_of_prefixLE S₁ S₂
    (duplicatedLeftSet S₁ S₂) (duplicatedRightSet S₁ S₂)
    (duplicatedForget_injOn_leftSet S₁ S₂)
    (duplicatedForget_injOn_rightSet S₁ S₂) hpos
  simpa only [duplicatedImage_leftSet, duplicatedImage_rightSet] using himage

lemma col_left_prefixLE_right_of_good {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (hgood : GoodSubset (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)) :
    T₁ ≼ₚ T₂ := by
  have hpos : rectangularColLeftSet S₁ S₂ T₁ T₂ hsize ≼ₚ
      castFinset hsize (duplicatedRightSet T₁ T₂) := by
    rw [← rectangularColLeftSet_compl]
    exact hgood
  have himage := rectangularColImage_prefixLE_of_prefixLE
    S₁ S₂ T₁ T₂ hsize
    (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)
    (castFinset hsize (duplicatedRightSet T₁ T₂))
    (rectangularColForget_injOn_leftSet S₁ S₂ T₁ T₂ hsize)
    (rectangularColForget_injOn_rightSet S₁ S₂ T₁ T₂ hsize) hpos
  simpa only [rectangularColImage_leftSet, rectangularColImage_rightSet] using himage

lemma left_bad_row_or_col_of_not_minorLE {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (hnot : ¬(S₁ ≼ₚ S₂ ∧ T₁ ≼ₚ T₂)) :
    ¬GoodSubset (duplicatedLeftSet S₁ S₂) ∨
      ¬GoodSubset (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize) := by
  by_contra h
  push Not at h
  exact hnot ⟨row_left_prefixLE_right_of_good S₁ S₂ h.1,
    col_left_prefixLE_right_of_good S₁ S₂ T₁ T₂ hsize h.2⟩

/-- Products allowed on the right-hand side of rectangular two-minor
straightening. -/
def twoMinorStraighteningGenerators {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m)) :
    Set (GenericPoly D n m) :=
  {x | ∃ A C : Finset (Fin n), ∃ B E : Finset (Fin m),
    A.card = B.card ∧ C.card = E.card ∧
    A ≼ₚ S₁ ∧ B ≼ₚ T₁ ∧ A ≼ₚ C ∧ B ≼ₚ E ∧
    (A ≺ₚ S₁ ∨ B ≺ₚ T₁) ∧
    A.card + C.card = S₁.card + S₂.card ∧
    x = finsetMinorPoly (D := D) A B * finsetMinorPoly (D := D) C E}

/-- Integral span of the output products in two-minor straightening. -/
def twoMinorStraighteningSpan {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m)) :
    AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure (twoMinorStraighteningGenerators (D := D) S₁ S₂ T₁ T₂)

lemma laplacePermSum_mem_twoMinorStraighteningSpan
    {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hsize : T₁.card + T₂.card = S₁.card + S₂.card)
    (hnot : ¬(S₁ ≼ₚ S₂ ∧ T₁ ≼ₚ T₂))
    (P Q : Finset (Fin (S₁.card + S₂.card)))
    (hcard : P.card = Q.card)
    (hPle : P ≼ₚ duplicatedLeftSet S₁ S₂)
    (hQle : Q ≼ₚ rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)
    (hPgood : GoodSubset P) (hQgood : GoodSubset Q) :
    laplacePermSum
        (rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize) P Q ∈
      twoMinorStraighteningSpan (D := D) S₁ S₂ T₁ T₂ := by
  classical
  let f := duplicatedForget S₁ S₂
  let g := rectangularColForget S₁ S₂ T₁ T₂ hsize
  let Y := rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize
  let H := twoMinorStraighteningSpan (D := D) S₁ S₂ T₁ T₂
  obtain ⟨u, hu⟩ :=
    exists_intUnit_mul_laplacePermSum_eq_mul_finsetMinor Y P Q hcard
  apply (intUnit_cast_mul_mem_iff H u (laplacePermSum Y P Q)).mp
  rw [hu]
  by_cases hinjP : Set.InjOn f P
  · by_cases hinjQ : Set.InjOn g Q
    · by_cases hinjPc : Set.InjOn f (Pᶜ : Finset (Fin (S₁.card + S₂.card)))
      · by_cases hinjQc : Set.InjOn g (Qᶜ : Finset (Fin (S₁.card + S₂.card)))
        · let A : Finset (Fin n) := P.image f
          let B : Finset (Fin m) := Q.image g
          let C : Finset (Fin n) := Pᶜ.image f
          let E : Finset (Fin m) := Qᶜ.image g
          have hAB : A.card = B.card := by
            dsimp [A, B]
            rw [Finset.card_image_iff.mpr hinjP,
              Finset.card_image_iff.mpr hinjQ, hcard]
          have hCE : C.card = E.card := by
            calc
              C.card = Pᶜ.card := Finset.card_image_iff.mpr hinjPc
              _ = Qᶜ.card := by
                simpa [Finset.card_compl] using
                  congrArg (fun k ↦ S₁.card + S₂.card - k) hcard
              _ = E.card := (Finset.card_image_iff.mpr hinjQc).symm
          have hAle : A ≼ₚ S₁ := by
            have h := duplicatedImage_prefixLE_of_prefixLE S₁ S₂
              P (duplicatedLeftSet S₁ S₂) hinjP
              (duplicatedForget_injOn_leftSet S₁ S₂) hPle
            rw [duplicatedImage_leftSet] at h
            change duplicatedImage S₁ S₂ P ≼ₚ S₁
            exact h
          have hBle : B ≼ₚ T₁ := by
            have h' := rectangularColImage_prefixLE_of_prefixLE
              S₁ S₂ T₁ T₂ hsize
              Q (rectangularColLeftSet S₁ S₂ T₁ T₂ hsize)
              hinjQ
              (rectangularColForget_injOn_leftSet S₁ S₂ T₁ T₂ hsize) hQle
            simpa [B, g] using h'
          have hAC : A ≼ₚ C := by
            have h := duplicatedImage_prefixLE_of_prefixLE S₁ S₂
              P Pᶜ hinjP hinjPc hPgood
            change duplicatedImage S₁ S₂ P ≼ₚ duplicatedImage S₁ S₂ Pᶜ
            exact h
          have hBE : B ≼ₚ E := by
            have h' := rectangularColImage_prefixLE_of_prefixLE
              S₁ S₂ T₁ T₂ hsize Q Qᶜ hinjQ hinjQc hQgood
            simpa [B, E, g] using h'
          have hstrict : A ≺ₚ S₁ ∨ B ≺ₚ T₁ := by
            rcases left_bad_row_or_col_of_not_minorLE
              S₁ S₂ T₁ T₂ hsize hnot with hrow | hcol
            · left
              have hne : P ≠ duplicatedLeftSet S₁ S₂ := by
                intro heq
                apply hrow
                simpa [heq] using hPgood
              have hs := duplicatedImage_prefixLT S₁ S₂ P hinjP ⟨hPle, hne⟩
              change duplicatedImage S₁ S₂ P ≺ₚ S₁
              exact hs
            · right
              have hne : Q ≠ rectangularColLeftSet S₁ S₂ T₁ T₂ hsize := by
                intro heq
                apply hcol
                simpa [heq] using hQgood
              have hs := rectangularColImage_prefixLT
                S₁ S₂ T₁ T₂ hsize Q hinjQ ⟨hQle, hne⟩
              simpa [B, g] using hs
          have htotal : A.card + C.card = S₁.card + S₂.card := by
            calc
              A.card + C.card = P.card + Pᶜ.card := by
                rw [Finset.card_image_iff.mpr hinjP,
                  Finset.card_image_iff.mpr hinjPc]
              _ = Fintype.card (Fin (S₁.card + S₂.card)) :=
                Finset.card_add_card_compl P
              _ = S₁.card + S₂.card := Fintype.card_fin _
          have hminor₁ : finsetMinor Y P Q =
              finsetMinorPoly (D := D) A B := by
            simpa [Y, A, B, f, g] using
              (finsetMinor_rectangularDuplicatedMatrix
                (D := D) S₁ S₂ T₁ T₂ hsize P Q hinjP hinjQ)
          have hminor₂ : finsetMinor Y Pᶜ Qᶜ =
              finsetMinorPoly (D := D) C E := by
            simpa [Y, C, E, f, g] using
              (finsetMinor_rectangularDuplicatedMatrix
                (D := D) S₁ S₂ T₁ T₂ hsize Pᶜ Qᶜ hinjPc hinjQc)
          apply AddSubgroup.subset_closure
          exact ⟨A, C, B, E, hAB, hCE, hAle, hBle, hAC, hBE,
            hstrict, htotal, congrArg₂ (· * ·) hminor₁ hminor₂⟩
        · have hz : finsetMinor Y Pᶜ Qᶜ = 0 := by
            change finsetMinor (Matrix.of fun i j ↦
              (MvPolynomial.X (f i, g j) : GenericPoly D n m)) Pᶜ Qᶜ = 0
            exact finsetMinor_pulled_eq_zero_of_not_injOn_right
              (fun i j ↦ (MvPolynomial.X (i, j) : GenericPoly D n m))
              f g Pᶜ Qᶜ hinjQc
          rw [hz, mul_zero]
          exact H.zero_mem
      · have hz : finsetMinor Y Pᶜ Qᶜ = 0 := by
          change finsetMinor (Matrix.of fun i j ↦
            (MvPolynomial.X (f i, g j) : GenericPoly D n m)) Pᶜ Qᶜ = 0
          exact finsetMinor_pulled_eq_zero_of_not_injOn_left
            (fun i j ↦ (MvPolynomial.X (i, j) : GenericPoly D n m))
            f g Pᶜ Qᶜ hinjPc
        rw [hz, mul_zero]
        exact H.zero_mem
    · have hz : finsetMinor Y P Q = 0 := by
        change finsetMinor (Matrix.of fun i j ↦
          (MvPolynomial.X (f i, g j) : GenericPoly D n m)) P Q = 0
        exact finsetMinor_pulled_eq_zero_of_not_injOn_right
          (fun i j ↦ (MvPolynomial.X (i, j) : GenericPoly D n m))
          f g P Q hinjQ
      rw [hz, zero_mul]
      exact H.zero_mem
  · have hz : finsetMinor Y P Q = 0 := by
      change finsetMinor (Matrix.of fun i j ↦
        (MvPolynomial.X (f i, g j) : GenericPoly D n m)) P Q = 0
      exact finsetMinor_pulled_eq_zero_of_not_injOn_left
        (fun i j ↦ (MvPolynomial.X (i, j) : GenericPoly D n m))
        f g P Q hinjP
    rw [hz, zero_mul]
    exact H.zero_mem

/-- Two-minor straightening for a rectangular generic matrix.  Membership in
the additive closure is precisely a finite integral linear combination of the
products described by `twoMinorStraighteningGenerators`. -/
theorem two_minor_straightening {D : Type*} [CommRing D] {n m : ℕ}
    (S₁ S₂ : Finset (Fin n)) (T₁ T₂ : Finset (Fin m))
    (hcard₁ : S₁.card = T₁.card) (hcard₂ : S₂.card = T₂.card)
    (hnot : ¬(S₁ ≼ₚ S₂ ∧ T₁ ≼ₚ T₂)) :
    finsetMinorPoly (D := D) S₁ T₁ * finsetMinorPoly (D := D) S₂ T₂ ∈
      twoMinorStraighteningSpan (D := D) S₁ S₂ T₁ T₂ := by
  classical
  have hsize : T₁.card + T₂.card = S₁.card + S₂.card := by omega
  let Y := rectangularDuplicatedMatrix (D := D) S₁ S₂ T₁ T₂ hsize
  let A := duplicatedLeftSet S₁ S₂
  let B := rectangularColLeftSet S₁ S₂ T₁ T₂ hsize
  let H := twoMinorStraighteningSpan (D := D) S₁ S₂ T₁ T₂
  have hAB : A.card = B.card := by
    dsimp [A, B, rectangularColLeftSet]
    rw [card_castFinset, card_duplicatedLeftSet, card_duplicatedLeftSet, hcard₁]
  have hlapSquare : laplacePermSum Y A B ∈ laplaceStraighteningSpan Y A B :=
    laplacePermSum_mem_straighteningSpan Y A B
  have hsquare_le : laplaceStraighteningSpan Y A B ≤ H := by
    apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases hx with ⟨P, Q, hPA, hQB, hPgood, hQgood, rfl⟩
    by_cases hPQ : P.card = Q.card
    · exact laplacePermSum_mem_twoMinorStraighteningSpan
        S₁ S₂ T₁ T₂ hsize hnot P Q hPQ hPA hQB hPgood hQgood
    · rw [laplacePermSum_eq_zero_of_card_ne Y P Q hPQ]
      exact H.zero_mem
  have hlap : laplacePermSum Y A B ∈ H := hsquare_le hlapSquare
  obtain ⟨u, hu⟩ :=
    exists_intUnit_mul_laplacePermSum_eq_mul_finsetMinor Y A B hAB
  have hleft : finsetMinor Y A B = finsetMinorPoly (D := D) S₁ T₁ := by
    simpa [Y, A, B] using
      (finsetMinor_rectangularDuplicatedMatrix_left
        (D := D) S₁ S₂ T₁ T₂ hsize)
  have hright : finsetMinor Y Aᶜ Bᶜ = finsetMinorPoly (D := D) S₂ T₂ := by
    rw [show Aᶜ = duplicatedRightSet S₁ S₂ by
        simpa [A] using duplicatedLeftSet_compl S₁ S₂,
      show Bᶜ = castFinset hsize (duplicatedRightSet T₁ T₂) by
        simpa [B] using rectangularColLeftSet_compl S₁ S₂ T₁ T₂ hsize]
    simpa [Y] using
      (finsetMinor_rectangularDuplicatedMatrix_right
        (D := D) S₁ S₂ T₁ T₂ hsize)
  have hulap : (u : GenericPoly D n m) * laplacePermSum Y A B ∈ H :=
    (intUnit_cast_mul_mem_iff H u (laplacePermSum Y A B)).mpr hlap
  rw [hu, hleft, hright] at hulap
  exact hulap

@[simp] lemma rowSet_of_finsetMinorIndex {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card = B.card) :
    (minorIndexOfFinsets A B hcard).rowSet = A :=
  rowSet_minorIndexOfFinsets A B hcard

@[simp] lemma colSet_of_finsetMinorIndex {n m : ℕ}
    (A : Finset (Fin n)) (B : Finset (Fin m)) (hcard : A.card = B.card) :
    (minorIndexOfFinsets A B hcard).colSet = B :=
  colSet_minorIndexOfFinsets A B hcard

end GenericMaximalMinor

end
end
end

section
section
/-!
# Standard products of minors

This file packages minors by their row and column sets and lifts the
two-minor straightening theorem to finite products.
-/

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

/-- A minor represented by equally large row and column subsets. -/
structure FinsetMinorIndex (n m : ℕ) where
  rows : Finset (Fin n)
  cols : Finset (Fin m)
  card_eq : rows.card = cols.card

instance (n m : ℕ) : DecidableEq (FinsetMinorIndex n m) := Classical.decEq _

def finsetMinorIndexEquiv (n m : ℕ) :
    FinsetMinorIndex n m ≃
      {p : Finset (Fin n) × Finset (Fin m) // p.1.card = p.2.card} where
  toFun d := ⟨(d.rows, d.cols), d.card_eq⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv := by intro d; cases d; rfl
  right_inv := by intro p; cases p; rfl

instance (n m : ℕ) : Fintype (FinsetMinorIndex n m) :=
  Fintype.ofEquiv
    {p : Finset (Fin n) × Finset (Fin m) // p.1.card = p.2.card}
    (finsetMinorIndexEquiv n m).symm

/-- The polynomial represented by a finite-set minor index. -/
def FinsetMinorIndex.poly {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) : GenericPoly D n m :=
  finsetMinorPoly (D := D) d.rows d.cols

/-- Componentwise prefix order on finite-set minor indices. -/
def FinsetMinorIndex.LE {n m : ℕ}
    (d e : FinsetMinorIndex n m) : Prop :=
  d.rows ≼ₚ e.rows ∧ d.cols ≼ₚ e.cols

scoped infix:50 " ≼ᵢ " => FinsetMinorIndex.LE

/-- Strict componentwise order: both coordinates weakly decrease and at least
one decreases strictly. -/
def FinsetMinorIndex.LT {n m : ℕ}
    (d e : FinsetMinorIndex n m) : Prop := d ≼ᵢ e ∧ d ≠ e

scoped infix:50 " ≺ᵢ " => FinsetMinorIndex.LT

lemma finsetMinorIndex_le_trans {n m : ℕ} {d e f : FinsetMinorIndex n m}
    (hde : d ≼ᵢ e) (hef : e ≼ᵢ f) : d ≼ᵢ f :=
  ⟨prefixLE_trans hde.1 hef.1, prefixLE_trans hde.2 hef.2⟩

lemma finsetMinorIndex_ext {n m : ℕ} {d e : FinsetMinorIndex n m}
    (hrows : d.rows = e.rows) (hcols : d.cols = e.cols) : d = e := by
  cases d
  cases e
  simp_all

/-- Defect used for the inner straightening induction. -/
def FinsetMinorIndex.defect {n m : ℕ} (d : FinsetMinorIndex n m) : ℕ :=
  prefixDefect d.rows + prefixDefect d.cols

lemma finsetMinorIndex_defect_lt_of_left_strict {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (hrow : d.rows ≺ₚ e.rows) (hcol : d.cols ≼ₚ e.cols) :
    d.defect < e.defect := by
  unfold FinsetMinorIndex.defect
  exact Nat.add_lt_add_of_lt_of_le
    (prefixDefect_lt_of_prefixLT hrow) (prefixDefect_le_of_prefixLE hcol)

lemma finsetMinorIndex_defect_lt_of_right_strict {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (hrow : d.rows ≼ₚ e.rows) (hcol : d.cols ≺ₚ e.cols) :
    d.defect < e.defect := by
  unfold FinsetMinorIndex.defect
  exact Nat.add_lt_add_of_le_of_lt
    (prefixDefect_le_of_prefixLE hrow) (prefixDefect_lt_of_prefixLT hcol)

lemma finsetMinorIndex_defect_lt_of_strict_coordinates {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (hrow : d.rows ≼ₚ e.rows) (hcol : d.cols ≼ₚ e.cols)
    (hstrict : d.rows ≺ₚ e.rows ∨ d.cols ≺ₚ e.cols) :
    d.defect < e.defect := by
  rcases hstrict with h | h
  · exact finsetMinorIndex_defect_lt_of_left_strict h hcol
  · exact finsetMinorIndex_defect_lt_of_right_strict hrow h

lemma finsetMinorIndex_defect_lt_of_LT {n m : ℕ}
    {d e : FinsetMinorIndex n m} (h : d ≺ᵢ e) :
    d.defect < e.defect := by
  apply finsetMinorIndex_defect_lt_of_strict_coordinates h.1.1 h.1.2
  by_cases hrows : d.rows = e.rows
  · right
    exact ⟨h.1.2, by
      intro hcols
      exact h.2 (finsetMinorIndex_ext hrows hcols)⟩
  · exact Or.inl ⟨h.1.1, hrows⟩

/-- A list is standard when consecutive minors are weakly increasing. -/
def IsStandardMinorList {n m : ℕ} : List (FinsetMinorIndex n m) → Prop
  | [] => True
  | [_] => True
  | d :: e :: l => d ≼ᵢ e ∧ IsStandardMinorList (e :: l)

/-- Polynomial product represented by a list of minors. -/
def minorListPoly {D : Type*} [CommRing D] {n m : ℕ} :
    List (FinsetMinorIndex n m) → GenericPoly D n m
  | [] => 1
  | d :: l => d.poly * minorListPoly l

@[simp] lemma minorListPoly_nil {D : Type*} [CommRing D] {n m : ℕ} :
    minorListPoly (D := D) ([] : List (FinsetMinorIndex n m)) = 1 := rfl

@[simp] lemma minorListPoly_cons {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) (d :: l) = d.poly * minorListPoly l := rfl

/-- Standard products with a fixed number of minor factors. -/
def standardMinorProductSpanOfLength {D : Type*} [CommRing D]
    (n m k : ℕ) : AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ l.length = k ∧
        x = minorListPoly (D := D) l}

lemma standard_minorListPoly_mem_spanOfLength
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (hl : IsStandardMinorList l) :
    minorListPoly (D := D) l ∈
      standardMinorProductSpanOfLength (D := D) n m l.length := by
  apply AddSubgroup.subset_closure
  exact ⟨l, hl, rfl, rfl⟩

lemma mul_left_mem_of_mem_closure {R : Type*} [CommRing R]
    (K : AddSubgroup R) (s : Set R) (c x : R)
    (hgen : ∀ y ∈ s, c * y ∈ K) (hx : x ∈ AddSubgroup.closure s) :
    c * x ∈ K := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using K.add_mem hx hy
  | neg x _ hx => simpa using K.neg_mem hx

lemma mul_right_mem_of_mem_closure {R : Type*} [CommRing R]
    (K : AddSubgroup R) (s : Set R) (c x : R)
    (hgen : ∀ y ∈ s, y * c ∈ K) (hx : x ∈ AddSubgroup.closure s) :
    x * c ∈ K := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using K.add_mem hx hy
  | neg x _ hx => simpa using K.neg_mem hx

/-- Allowed replacements of a nonstandard pair. -/
def pairReductionGenerators {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) : Set (GenericPoly D n m) :=
  {x | ∃ a b : FinsetMinorIndex n m,
    a ≺ᵢ d ∧ a ≼ᵢ b ∧ x = a.poly * b.poly}

def pairReductionSpan {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) : AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure (pairReductionGenerators (D := D) d)

lemma two_minor_mem_pairReductionSpan {D : Type*} [CommRing D] {n m : ℕ}
    (d e : FinsetMinorIndex n m) (hnot : ¬d ≼ᵢ e) :
    d.poly * e.poly ∈ pairReductionSpan (D := D) d := by
  have h := two_minor_straightening (D := D)
    d.rows e.rows d.cols e.cols d.card_eq e.card_eq hnot
  apply (AddSubgroup.closure_le _).mpr ?_ h
  intro x hx
  rcases hx with ⟨A, C, B, E, hAB, hCE, hAd, hBd,
    hAC, hBE, hstrict, -, rfl⟩
  let a : FinsetMinorIndex n m := ⟨A, B, hAB⟩
  let b : FinsetMinorIndex n m := ⟨C, E, hCE⟩
  apply AddSubgroup.subset_closure
  refine ⟨a, b, ?_, ⟨hAC, hBE⟩, rfl⟩
  refine ⟨⟨hAd, hBd⟩, ?_⟩
  intro hab
  have hrows : A = d.rows := congrArg FinsetMinorIndex.rows hab
  have hcols : B = d.cols := congrArg FinsetMinorIndex.cols hab
  rcases hstrict with hs | hs
  · exact hs.2 hrows
  · exact hs.2 hcols

/-- Every finite product of minors straightens into standard products with the
same number of factors. -/
theorem minorListPoly_mem_standardSpanOfLength
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) l ∈
      standardMinorProductSpanOfLength (D := D) n m l.length := by
  classical
  generalize hk : l.length = k
  induction k using Nat.strong_induction_on generalizing l with
  | h k outer =>
      cases l with
      | nil =>
          have hk0 : k = 0 := by simpa using hk.symm
          subst k
          exact standard_minorListPoly_mem_spanOfLength
            (D := D) (n := n) (m := m) [] trivial
      | cons d t =>
          have htlen : t.length < k := by
            simp only [List.length_cons] at hk
            omega
          have prepend : ∀ (a : FinsetMinorIndex n m)
              (s : List (FinsetMinorIndex n m)),
              IsStandardMinorList s → s.length < k →
              minorListPoly (D := D) (a :: s) ∈
                standardMinorProductSpanOfLength (D := D) n m (s.length + 1) := by
            intro a s hs hslen
            generalize hdef : a.defect = q
            induction q using Nat.strong_induction_on generalizing a s with
            | h q inner =>
                cases s with
                | nil =>
                    exact standard_minorListPoly_mem_spanOfLength
                      (D := D) (n := n) (m := m) [a] trivial
                | cons b r =>
                    by_cases hab : a ≼ᵢ b
                    · apply AddSubgroup.subset_closure
                      exact ⟨a :: b :: r, ⟨hab, hs⟩, rfl, rfl⟩
                    · have hpair := two_minor_mem_pairReductionSpan
                        (D := D) a b hab
                      have hpairTail :
                          (a.poly * b.poly) * minorListPoly (D := D) r ∈
                            standardMinorProductSpanOfLength
                              (D := D) n m ((b :: r).length + 1) := by
                        apply mul_right_mem_of_mem_closure
                          (standardMinorProductSpanOfLength
                            (D := D) n m ((b :: r).length + 1))
                          (pairReductionGenerators (D := D) a)
                          (minorListPoly (D := D) r) (a.poly * b.poly)
                        · intro y hy
                          rcases hy with ⟨a', b', ha'a, ha'b', rfl⟩
                          have htail : minorListPoly (D := D) (b' :: r) ∈
                              standardMinorProductSpanOfLength
                                (D := D) n m (b' :: r).length := by
                            exact outer (b' :: r).length (by simpa using hslen)
                              (b' :: r) rfl
                          rw [mul_assoc]
                          change a'.poly * minorListPoly (D := D) (b' :: r) ∈
                            standardMinorProductSpanOfLength
                              (D := D) n m ((b :: r).length + 1)
                          apply mul_left_mem_of_mem_closure
                            (standardMinorProductSpanOfLength
                              (D := D) n m ((b :: r).length + 1))
                            {x | ∃ u : List (FinsetMinorIndex n m),
                              IsStandardMinorList u ∧
                              u.length = (b' :: r).length ∧
                              x = minorListPoly (D := D) u}
                            a'.poly (minorListPoly (D := D) (b' :: r))
                          · intro z hz
                            rcases hz with ⟨u, huStd, huLen, rfl⟩
                            have hdeflt : a'.defect < q :=
                              (finsetMinorIndex_defect_lt_of_LT ha'a).trans_eq hdef
                            have hpre := inner a'.defect hdeflt a' u huStd (by
                              simpa [huLen] using hslen)
                            simpa [huLen] using hpre
                          · exact htail
                        · exact hpair
                      simpa [minorListPoly, mul_assoc] using hpairTail
          have htail := outer t.length htlen t rfl
          have hcons : minorListPoly (D := D) (d :: t) ∈
              standardMinorProductSpanOfLength (D := D) n m (t.length + 1) := by
            apply mul_left_mem_of_mem_closure
              (standardMinorProductSpanOfLength (D := D) n m (t.length + 1))
              {x | ∃ s : List (FinsetMinorIndex n m),
                IsStandardMinorList s ∧ s.length = t.length ∧
                  x = minorListPoly (D := D) s}
              d.poly (minorListPoly (D := D) t)
            · intro x hx
              rcases hx with ⟨s, hs, hslen, rfl⟩
              have hp := prepend d s hs (by simpa [hslen] using htlen)
              simpa [hslen] using hp
            · exact htail
          have hk' : t.length + 1 = k := by simpa using hk
          rw [hk'] at hcons
          exact hcons

/-! ## Spanning the polynomial ring -/

/-- The coefficient-linear span of standard products. -/
def standardMinorProductSubmodule (D : Type*) [CommRing D] (n m : ℕ) :
    Submodule D (GenericPoly D n m) :=
  Submodule.span D
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ x = minorListPoly (D := D) l}

lemma minorListPoly_append {D : Type*} [CommRing D] {n m : ℕ}
    (l₁ l₂ : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) (l₁ ++ l₂) =
      minorListPoly (D := D) l₁ * minorListPoly (D := D) l₂ := by
  induction l₁ with
  | nil => simp
  | cons d l ih => simp [ih, mul_assoc]

lemma minorListPoly_mem_standardSubmodule
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) l ∈ standardMinorProductSubmodule D n m := by
  have hlen := minorListPoly_mem_standardSpanOfLength (D := D) l
  apply (AddSubgroup.closure_le
    (standardMinorProductSubmodule D n m).toAddSubgroup).mpr ?_ hlen
  intro x hx
  rcases hx with ⟨u, huStd, -, rfl⟩
  apply Submodule.subset_span
  exact ⟨u, huStd, rfl⟩

lemma standardSubmodule_mul_minor
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) {x : GenericPoly D n m}
    (hx : x ∈ standardMinorProductSubmodule D n m) :
    x * d.poly ∈ standardMinorProductSubmodule D n m := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨l, hl, rfl⟩
      have hlist := minorListPoly_mem_standardSubmodule
        (D := D) (l ++ [d])
      rw [minorListPoly_append] at hlist
      simpa using hlist
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using
      (standardMinorProductSubmodule D n m).add_mem hx hy
  | smul a x _ hx =>
      rw [smul_mul_assoc]
      exact (standardMinorProductSubmodule D n m).smul_mem a hx

/-- The `1 × 1` minor at `(i,j)`. -/
def singletonMinorIndex {n m : ℕ} (i : Fin n) (j : Fin m) :
    FinsetMinorIndex n m where
  rows := {i}
  cols := {j}
  card_eq := by simp

@[simp] lemma singletonMinorIndex_poly {D : Type*} [CommRing D]
    {n m : ℕ} (i : Fin n) (j : Fin m) :
    (singletonMinorIndex i j).poly =
      (MvPolynomial.X (i, j) : GenericPoly D n m) := by
  unfold FinsetMinorIndex.poly singletonMinorIndex finsetMinorPoly
  rw [dif_pos ((Finset.card_singleton i).trans (Finset.card_singleton j).symm)]
  unfold minorPoly minorMatrix
  let M : Matrix (Fin ({i} : Finset (Fin n)).card)
      (Fin ({i} : Finset (Fin n)).card) (GenericPoly D n m) :=
    fun a b ↦ MvPolynomial.X
      ((({i} : Finset (Fin n)).orderEmbOfFin rfl) a,
        (({j} : Finset (Fin m)).orderEmbOfFin (by simp)) b)
  let e : Fin ({i} : Finset (Fin n)).card ≃ Fin 1 :=
    (Fin.castOrderIso (Finset.card_singleton i)).toEquiv
  change Matrix.det M = MvPolynomial.X (i, j)
  calc
    Matrix.det M = Matrix.det (M.reindex e e) :=
      (Matrix.det_reindex_self e M).symm
    _ = (M.reindex e e) 0 0 := Matrix.det_fin_one _
    _ = MvPolynomial.X (i, j) := by
      change MvPolynomial.X
        ((({i} : Finset (Fin n)).orderEmbOfFin rfl) (e.symm 0),
          (({j} : Finset (Fin m)).orderEmbOfFin (by simp)) (e.symm 0)) = _
      have hi : (({i} : Finset (Fin n)).orderEmbOfFin rfl) (e.symm 0) = i :=
        Finset.mem_singleton.mp
          (Finset.orderEmbOfFin_mem ({i} : Finset (Fin n)) rfl (e.symm 0))
      have hj : (({j} : Finset (Fin m)).orderEmbOfFin (by simp)) (e.symm 0) = j :=
        Finset.mem_singleton.mp
          (Finset.orderEmbOfFin_mem ({j} : Finset (Fin m)) (by simp) (e.symm 0))
      rw [hi, hj]

/-- Standard products span the entire generic polynomial ring over its
coefficient ring. -/
theorem mem_standardMinorProductSubmodule
    {D : Type*} [CommRing D] {n m : ℕ} (p : GenericPoly D n m) :
    p ∈ standardMinorProductSubmodule D n m := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hone : (1 : GenericPoly D n m) ∈
          standardMinorProductSubmodule D n m :=
        minorListPoly_mem_standardSubmodule (D := D) []
      have ha := (standardMinorProductSubmodule D n m).smul_mem a hone
      rw [MvPolynomial.smul_eq_C_mul, mul_one] at ha
      exact ha
  | add p q hp hq =>
      exact (standardMinorProductSubmodule D n m).add_mem hp hq
  | mul_X p ij hp =>
      simpa using standardSubmodule_mul_minor
        (D := D) (singletonMinorIndex ij.1 ij.2) hp

theorem standardMinorProductSubmodule_eq_top
    (D : Type*) [CommRing D] (n m : ℕ) :
    standardMinorProductSubmodule D n m = ⊤ := by
  apply top_unique
  intro p _
  exact mem_standardMinorProductSubmodule p

end GenericMaximalMinor

end
end
end

section
section
/-!
# Diagonal codes for standard products of minors

This file develops the combinatorial half of linear independence for standard
products.  A minor is read in increasing row and column order.  At a fixed
position `q`, a standard list gives a weakly increasing column; consequently
the multiset of entries occurring in that column determines their order.
-/

noncomputable section

open scoped BigOperators MonomialOrder

namespace GenericMaximalMinor

/-- A standard list is pairwise ordered, not merely ordered at adjacent
positions. -/
lemma isStandardMinorList_pairwise {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : IsStandardMinorList l) :
    l.Pairwise (· ≼ᵢ ·) := by
  induction l with
  | nil => simp
  | cons d l ih =>
      cases l with
      | nil => simp
      | cons e l =>
          have hde : d ≼ᵢ e := hl.1
          have htail : IsStandardMinorList (e :: l) := hl.2
          have hpair : (e :: l).Pairwise (· ≼ᵢ ·) := ih htail
          rw [List.pairwise_cons]
          refine ⟨?_, hpair⟩
          intro f hf
          simp only [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact hde
          · exact finsetMinorIndex_le_trans hde
              ((List.pairwise_cons.mp hpair).1 f hf)

lemma rows_card_anti_of_finsetMinorIndex_le {n m : ℕ}
    {d e : FinsetMinorIndex n m} (hde : d ≼ᵢ e) :
    e.rows.card ≤ d.rows.card :=
  card_ge_of_prefixLE hde.1

lemma cols_card_anti_of_finsetMinorIndex_le {n m : ℕ}
    {d e : FinsetMinorIndex n m} (hde : d ≼ᵢ e) :
    e.cols.card ≤ d.cols.card :=
  card_ge_of_prefixLE hde.2

/-- The `q`-th row entry of a minor, when it exists. -/
def FinsetMinorIndex.rowAt? {n m : ℕ} (d : FinsetMinorIndex n m)
    (q : ℕ) : Option (Fin n) :=
  if hq : q < d.rows.card then
    some (d.rows.orderEmbOfFin rfl ⟨q, hq⟩)
  else none

/-- The `q`-th column entry of a minor, when it exists. -/
def FinsetMinorIndex.colAt? {n m : ℕ} (d : FinsetMinorIndex n m)
    (q : ℕ) : Option (Fin m) :=
  if hq : q < d.cols.card then
    some (d.cols.orderEmbOfFin rfl ⟨q, hq⟩)
  else none

@[simp] lemma FinsetMinorIndex.rowAt?_eq_some {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : ℕ) (hq : q < d.rows.card) :
    d.rowAt? q = some (d.rows.orderEmbOfFin rfl ⟨q, hq⟩) := by
  simp [FinsetMinorIndex.rowAt?, hq]

@[simp] lemma FinsetMinorIndex.rowAt?_eq_none {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : ℕ) (hq : d.rows.card ≤ q) :
    d.rowAt? q = none := by
  simp [FinsetMinorIndex.rowAt?, hq]

@[simp] lemma FinsetMinorIndex.colAt?_eq_some {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : ℕ) (hq : q < d.cols.card) :
    d.colAt? q = some (d.cols.orderEmbOfFin rfl ⟨q, hq⟩) := by
  simp [FinsetMinorIndex.colAt?, hq]

@[simp] lemma FinsetMinorIndex.colAt?_eq_none {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : ℕ) (hq : d.cols.card ≤ q) :
    d.colAt? q = none := by
  simp [FinsetMinorIndex.colAt?, hq]

/-- The existing `q`-th row entries, in factor order. -/
def minorRowColumn {n m : ℕ} (l : List (FinsetMinorIndex n m))
    (q : ℕ) : List (Fin n) :=
  l.filterMap (fun d ↦ d.rowAt? q)

/-- The existing `q`-th column entries, in factor order. -/
def minorColColumn {n m : ℕ} (l : List (FinsetMinorIndex n m))
    (q : ℕ) : List (Fin m) :=
  l.filterMap (fun d ↦ d.colAt? q)

lemma rowAt?_mono_of_finsetMinorIndex_le {n m : ℕ}
    {d e : FinsetMinorIndex n m} (hde : d ≼ᵢ e) {q : ℕ}
    {a b : Fin n} (hda : d.rowAt? q = some a)
    (heb : e.rowAt? q = some b) : a ≤ b := by
  by_cases hdq : q < d.rows.card
  · simp only [FinsetMinorIndex.rowAt?, hdq, dite_true,
      Option.some.injEq] at hda
    by_cases heq : q < e.rows.card
    · simp only [FinsetMinorIndex.rowAt?, heq, dite_true,
        Option.some.injEq] at heb
      subst a
      subst b
      simpa using orderEmbOfFin_le_of_prefixLE hde.1 ⟨q, heq⟩
    · simp [FinsetMinorIndex.rowAt?, heq] at heb
  · simp [FinsetMinorIndex.rowAt?, hdq] at hda

lemma colAt?_mono_of_finsetMinorIndex_le {n m : ℕ}
    {d e : FinsetMinorIndex n m} (hde : d ≼ᵢ e) {q : ℕ}
    {a b : Fin m} (hda : d.colAt? q = some a)
    (heb : e.colAt? q = some b) : a ≤ b := by
  by_cases hdq : q < d.cols.card
  · simp only [FinsetMinorIndex.colAt?, hdq, dite_true,
      Option.some.injEq] at hda
    by_cases heq : q < e.cols.card
    · simp only [FinsetMinorIndex.colAt?, heq, dite_true,
        Option.some.injEq] at heb
      subst a
      subst b
      simpa using orderEmbOfFin_le_of_prefixLE hde.2 ⟨q, heq⟩
    · simp [FinsetMinorIndex.colAt?, heq] at heb
  · simp [FinsetMinorIndex.colAt?, hdq] at hda

/-- Every row-column read from a standard product is sorted. -/
lemma minorRowColumn_sorted {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : IsStandardMinorList l)
    (q : ℕ) : (minorRowColumn l q).SortedLE := by
  unfold minorRowColumn
  exact (List.Pairwise.filterMap (fun d ↦ d.rowAt? q)
    (fun d e hde a hda b heb ↦
      rowAt?_mono_of_finsetMinorIndex_le hde hda heb)
    (isStandardMinorList_pairwise hl)).sortedLE

/-- Every column-column read from a standard product is sorted. -/
lemma minorColColumn_sorted {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : IsStandardMinorList l)
    (q : ℕ) : (minorColColumn l q).SortedLE := by
  unfold minorColColumn
  exact (List.Pairwise.filterMap (fun d ↦ d.colAt? q)
    (fun d e hde a hda b heb ↦
      colAt?_mono_of_finsetMinorIndex_le hde hda heb)
    (isStandardMinorList_pairwise hl)).sortedLE

/-- The multiset-valued diagonal code of a list of minors.  This is exactly
the exponent data that will occur in the `Y` variables of the leading
monomial after the `X ↦ YZ` substitution. -/
def minorRowProfile {n m : ℕ} (l : List (FinsetMinorIndex n m)) :
    ℕ → Multiset (Fin n) :=
  fun q ↦ (minorRowColumn l q : Multiset (Fin n))

/-- Column half of the diagonal exponent data. -/
def minorColProfile {n m : ℕ} (l : List (FinsetMinorIndex n m)) :
    ℕ → Multiset (Fin m) :=
  fun q ↦ (minorColColumn l q : Multiset (Fin m))

lemma minorRowColumn_eq_of_profile_eq_of_standard {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hl₁ : IsStandardMinorList l₁) (hl₂ : IsStandardMinorList l₂)
    (hprofile : minorRowProfile l₁ = minorRowProfile l₂) (q : ℕ) :
    minorRowColumn l₁ q = minorRowColumn l₂ q := by
  apply List.Perm.eq_of_sortedLE (minorRowColumn_sorted hl₁ q)
    (minorRowColumn_sorted hl₂ q)
  rw [← Multiset.coe_eq_coe]
  exact congrFun hprofile q

lemma minorColColumn_eq_of_profile_eq_of_standard {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hl₁ : IsStandardMinorList l₁) (hl₂ : IsStandardMinorList l₂)
    (hprofile : minorColProfile l₁ = minorColProfile l₂) (q : ℕ) :
    minorColColumn l₁ q = minorColColumn l₂ q := by
  apply List.Perm.eq_of_sortedLE (minorColColumn_sorted hl₁ q)
    (minorColColumn_sorted hl₂ q)
  rw [← Multiset.coe_eq_coe]
  exact congrFun hprofile q

/-- For a list whose minor sizes weakly decrease, filtering out the factors
which have no `q`-th row does not shift any later existing entry: once one
factor is too short, every later factor is too short. -/
lemma minorRowColumn_get?_eq {n m : ℕ}
    {l : List (FinsetMinorIndex n m)}
    (hl : l.Pairwise (· ≼ᵢ ·)) (i q : ℕ) :
    (minorRowColumn l q)[i]? =
      l[i]?.bind (fun d ↦ d.rowAt? q) := by
  induction l generalizing i with
  | nil => simp [minorRowColumn]
  | cons d l ih =>
      have hhead := (List.pairwise_cons.mp hl).1
      have htail := (List.pairwise_cons.mp hl).2
      by_cases hq : q < d.rows.card
      · cases i with
        | zero => simp [minorRowColumn, FinsetMinorIndex.rowAt?, hq]
        | succ i =>
            simpa [minorRowColumn, FinsetMinorIndex.rowAt?, hq] using
              ih htail i
      · have hq' : d.rows.card ≤ q := Nat.le_of_not_gt hq
        have hall : ∀ e ∈ l, e.rows.card ≤ q := by
          intro e he
          exact (rows_card_anti_of_finsetMinorIndex_le
            (hhead e he)).trans hq'
        have hnone : minorRowColumn l q = [] := by
          rw [minorRowColumn, List.filterMap_eq_nil_iff]
          intro e he
          exact e.rowAt?_eq_none q (hall e he)
        have hout : minorRowColumn (d :: l) q = [] := by
          simpa only [minorRowColumn, List.filterMap_cons,
            d.rowAt?_eq_none q hq'] using hnone
        cases i with
        | zero => simp [hout, FinsetMinorIndex.rowAt?, hq]
        | succ i =>
            have hi := ih htail i
            rw [hnone] at hi
            rw [hout]
            simpa using hi

lemma minorColColumn_get?_eq {n m : ℕ}
    {l : List (FinsetMinorIndex n m)}
    (hl : l.Pairwise (· ≼ᵢ ·)) (i q : ℕ) :
    (minorColColumn l q)[i]? =
      l[i]?.bind (fun d ↦ d.colAt? q) := by
  induction l generalizing i with
  | nil => simp [minorColColumn]
  | cons d l ih =>
      have hhead := (List.pairwise_cons.mp hl).1
      have htail := (List.pairwise_cons.mp hl).2
      by_cases hq : q < d.cols.card
      · cases i with
        | zero => simp [minorColColumn, FinsetMinorIndex.colAt?, hq]
        | succ i =>
            simpa [minorColColumn, FinsetMinorIndex.colAt?, hq] using
              ih htail i
      · have hq' : d.cols.card ≤ q := Nat.le_of_not_gt hq
        have hall : ∀ e ∈ l, e.cols.card ≤ q := by
          intro e he
          exact (cols_card_anti_of_finsetMinorIndex_le
            (hhead e he)).trans hq'
        have hnone : minorColColumn l q = [] := by
          rw [minorColColumn, List.filterMap_eq_nil_iff]
          intro e he
          exact e.colAt?_eq_none q (hall e he)
        have hout : minorColColumn (d :: l) q = [] := by
          simpa only [minorColColumn, List.filterMap_cons,
            d.colAt?_eq_none q hq'] using hnone
        cases i with
        | zero => simp [hout, FinsetMinorIndex.colAt?, hq]
        | succ i =>
            have hi := ih htail i
            rw [hnone] at hi
            rw [hout]
            simpa using hi

/-- Empty minors represent the unit and are therefore omitted from the
indexing family for linear independence. -/
def HasNoEmptyMinors {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) : Prop :=
  ∀ d ∈ l, d.rows.Nonempty

lemma minorRowColumn_zero_length {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : HasNoEmptyMinors l) :
    (minorRowColumn l 0).length = l.length := by
  revert hl
  induction l with
  | nil => intro; simp [minorRowColumn]
  | cons d l ih =>
      intro hl
      have hd : 0 < d.rows.card := Finset.card_pos.mpr (hl d (by simp))
      have htail : HasNoEmptyMinors l := by
        intro e he
        exact hl e (by simp [he])
      change
        (List.filterMap (fun e ↦ e.rowAt? 0) (d :: l)).length =
          (d :: l).length
      rw [List.filterMap_cons, d.rowAt?_eq_some 0 hd]
      simp only [List.length_cons]
      exact congrArg Nat.succ (ih htail)

lemma rows_eq_of_rowAt?_eq {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (h : ∀ q : ℕ, d.rowAt? q = e.rowAt? q) : d.rows = e.rows := by
  have hnotlt₁ : ¬d.rows.card < e.rows.card := by
    intro hlt
    have hq := h d.rows.card
    simp [FinsetMinorIndex.rowAt?, hlt] at hq
  have hnotlt₂ : ¬e.rows.card < d.rows.card := by
    intro hlt
    have hq := h e.rows.card
    simp [FinsetMinorIndex.rowAt?, hlt] at hq
  have hcard : d.rows.card = e.rows.card := by omega
  have hpoint (q : Fin d.rows.card) :
      d.rows.orderEmbOfFin rfl q =
        e.rows.orderEmbOfFin rfl
          ⟨q.val, by simpa [hcard] using q.isLt⟩ := by
    let qe : Fin e.rows.card :=
      ⟨q.val, by simpa [hcard] using q.isLt⟩
    have hdq : d.rowAt? q.val = some (d.rows.orderEmbOfFin rfl q) := by
      simpa using d.rowAt?_eq_some q.val q.isLt
    have heq : e.rowAt? q.val = some (e.rows.orderEmbOfFin rfl qe) := by
      simpa using e.rowAt?_eq_some q.val qe.isLt
    have hq := h q.val
    rw [hdq, heq] at hq
    exact Option.some.inj hq
  apply Finset.Subset.antisymm
  · intro x hx
    have hxset : x ∈ (d.rows : Set (Fin n)) := hx
    rw [← d.rows.range_orderEmbOfFin rfl] at hxset
    obtain ⟨q, rfl⟩ := hxset
    rw [hpoint q]
    exact e.rows.orderEmbOfFin_mem rfl _
  · intro x hx
    have hxset : x ∈ (e.rows : Set (Fin n)) := hx
    rw [← e.rows.range_orderEmbOfFin rfl] at hxset
    obtain ⟨q, rfl⟩ := hxset
    let qd : Fin d.rows.card := ⟨q.val, by simpa [hcard] using q.isLt⟩
    have hp := hpoint qd
    have hqe : (⟨qd.val, by simpa [hcard] using qd.isLt⟩ :
        Fin e.rows.card) = q := Fin.ext rfl
    rw [hqe] at hp
    rw [← hp]
    exact d.rows.orderEmbOfFin_mem rfl qd

lemma cols_eq_of_colAt?_eq {n m : ℕ}
    {d e : FinsetMinorIndex n m}
    (h : ∀ q : ℕ, d.colAt? q = e.colAt? q) : d.cols = e.cols := by
  have hnotlt₁ : ¬d.cols.card < e.cols.card := by
    intro hlt
    have hq := h d.cols.card
    simp [FinsetMinorIndex.colAt?, hlt] at hq
  have hnotlt₂ : ¬e.cols.card < d.cols.card := by
    intro hlt
    have hq := h e.cols.card
    simp [FinsetMinorIndex.colAt?, hlt] at hq
  have hcard : d.cols.card = e.cols.card := by omega
  have hpoint (q : Fin d.cols.card) :
      d.cols.orderEmbOfFin rfl q =
        e.cols.orderEmbOfFin rfl
          ⟨q.val, by simpa [hcard] using q.isLt⟩ := by
    let qe : Fin e.cols.card :=
      ⟨q.val, by simpa [hcard] using q.isLt⟩
    have hdq : d.colAt? q.val = some (d.cols.orderEmbOfFin rfl q) := by
      simpa using d.colAt?_eq_some q.val q.isLt
    have heq : e.colAt? q.val = some (e.cols.orderEmbOfFin rfl qe) := by
      simpa using e.colAt?_eq_some q.val qe.isLt
    have hq := h q.val
    rw [hdq, heq] at hq
    exact Option.some.inj hq
  apply Finset.Subset.antisymm
  · intro x hx
    have hxset : x ∈ (d.cols : Set (Fin m)) := hx
    rw [← d.cols.range_orderEmbOfFin rfl] at hxset
    obtain ⟨q, rfl⟩ := hxset
    rw [hpoint q]
    exact e.cols.orderEmbOfFin_mem rfl _
  · intro x hx
    have hxset : x ∈ (e.cols : Set (Fin m)) := hx
    rw [← e.cols.range_orderEmbOfFin rfl] at hxset
    obtain ⟨q, rfl⟩ := hxset
    let qd : Fin d.cols.card := ⟨q.val, by simpa [hcard] using q.isLt⟩
    have hp := hpoint qd
    have hqe : (⟨qd.val, by simpa [hcard] using qd.isLt⟩ :
        Fin e.cols.card) = q := Fin.ext rfl
    rw [hqe] at hp
    rw [← hp]
    exact d.cols.orderEmbOfFin_mem rfl qd

/-- A standard list of nonempty minors is uniquely determined by the row and
column exponent profiles of its diagonal monomial. -/
theorem eq_of_standard_minor_profiles {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hl₁ : IsStandardMinorList l₁) (hl₂ : IsStandardMinorList l₂)
    (hne₁ : HasNoEmptyMinors l₁) (hne₂ : HasNoEmptyMinors l₂)
    (hrow : minorRowProfile l₁ = minorRowProfile l₂)
    (hcol : minorColProfile l₁ = minorColProfile l₂) : l₁ = l₂ := by
  have hrowColumn : ∀ q, minorRowColumn l₁ q = minorRowColumn l₂ q :=
    minorRowColumn_eq_of_profile_eq_of_standard hl₁ hl₂ hrow
  have hcolColumn : ∀ q, minorColColumn l₁ q = minorColColumn l₂ q :=
    minorColColumn_eq_of_profile_eq_of_standard hl₁ hl₂ hcol
  have hlen : l₁.length = l₂.length := by
    calc
      l₁.length = (minorRowColumn l₁ 0).length :=
        (minorRowColumn_zero_length hne₁).symm
      _ = (minorRowColumn l₂ 0).length := by rw [hrowColumn 0]
      _ = l₂.length := minorRowColumn_zero_length hne₂
  apply List.ext_get hlen
  intro i hi₁ hi₂
  let d₁ := l₁.get ⟨i, hi₁⟩
  let d₂ := l₂.get ⟨i, hi₂⟩
  have hrowAt : ∀ q, d₁.rowAt? q = d₂.rowAt? q := by
    intro q
    have hg₁ := minorRowColumn_get?_eq
      (isStandardMinorList_pairwise hl₁) i q
    have hg₂ := minorRowColumn_get?_eq
      (isStandardMinorList_pairwise hl₂) i q
    rw [List.getElem?_eq_getElem hi₁] at hg₁
    rw [List.getElem?_eq_getElem hi₂] at hg₂
    simpa [d₁, d₂] using
      hg₁.symm.trans ((congrArg (fun s ↦ s[i]?) (hrowColumn q)).trans hg₂)
  have hcolAt : ∀ q, d₁.colAt? q = d₂.colAt? q := by
    intro q
    have hg₁ := minorColColumn_get?_eq
      (isStandardMinorList_pairwise hl₁) i q
    have hg₂ := minorColColumn_get?_eq
      (isStandardMinorList_pairwise hl₂) i q
    rw [List.getElem?_eq_getElem hi₁] at hg₁
    rw [List.getElem?_eq_getElem hi₂] at hg₂
    simpa [d₁, d₂] using
      hg₁.symm.trans ((congrArg (fun s ↦ s[i]?) (hcolColumn q)).trans hg₂)
  exact finsetMinorIndex_ext (rows_eq_of_rowAt?_eq hrowAt)
    (cols_eq_of_colAt?_eq hcolAt)

/-- Variables in the auxiliary `Y,Z` ring, ordered in blocks indexed by the
inner matrix coordinate. -/
abbrev StandardAuxVar (n m : ℕ) := Fin n ×ₗ (Fin n ⊕ₗ Fin m)

abbrev StandardAuxPoly (D : Type*) [CommSemiring D] (n m : ℕ) :=
  MvPolynomial (StandardAuxVar n m) D

def standardAuxYVar {n m : ℕ} (q i : Fin n) : StandardAuxVar n m :=
  toLex (q, toLex (Sum.inl i))

def standardAuxZVar {n m : ℕ} (q : Fin n) (j : Fin m) :
    StandardAuxVar n m :=
  toLex (q, toLex (Sum.inr j))

lemma Equiv.Perm.exists_first_moved_up {p : ℕ}
    (u : Equiv.Perm (Fin p)) (hu : u ≠ 1) :
    ∃ i : Fin p, (∀ j, j < i → u j = j) ∧ i < u i := by
  let moved : Finset (Fin p) := Finset.univ.filter fun i ↦ u i ≠ i
  have hmoved : moved.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hu
    apply Equiv.ext
    intro i
    have hi : i ∉ moved := by simp [hempty]
    simpa [moved] using hi
  let i := moved.min' hmoved
  have hiMoved : u i ≠ i := by
    have hi := moved.min'_mem hmoved
    simpa [moved] using hi
  have hprev : ∀ j, j < i → u j = j := by
    intro j hji
    by_contra hj
    have hjmem : j ∈ moved := by simp [moved, hj]
    have hmin : i ≤ j := moved.min'_le j hjmem
    exact (not_le_of_gt hji) hmin
  refine ⟨i, hprev, ?_⟩
  have hnotlt : ¬u i < i := by
    intro hui
    have hfix : u (u i) = u i := hprev (u i) hui
    exact hiMoved (u.injective hfix)
  exact lt_of_le_of_ne (le_of_not_gt hnotlt) hiMoved.symm

/-- A strictly increasing choice of `p` elements of `Fin n` which is not the
initial choice first moves to the right. -/
lemma OrderEmbedding.Fin.exists_first_ne_castLE_up {p n : ℕ} (hpn : p ≤ n)
    (q : Fin p ↪o Fin n) (hq : q ≠ Fin.castLEOrderEmb hpn) :
    ∃ i : Fin p,
      (∀ j, j < i → q j = Fin.castLEOrderEmb hpn j) ∧
        Fin.castLEOrderEmb hpn i < q i := by
  let moved : Finset (Fin p) := Finset.univ.filter fun i ↦
    q i ≠ Fin.castLEOrderEmb hpn i
  have hmoved : moved.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hq
    apply RelEmbedding.ext
    intro i
    by_contra hi
    have himem : i ∈ moved := Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hi⟩
    simpa [hempty] using himem
  let i := moved.min' hmoved
  have hiMoved : q i ≠ Fin.castLEOrderEmb hpn i := by
    have hi := moved.min'_mem hmoved
    exact (Finset.mem_filter.mp hi).2
  have hprev : ∀ j, j < i → q j = Fin.castLEOrderEmb hpn j := by
    intro j hji
    by_contra hj
    have hjmem : j ∈ moved := Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hj⟩
    have hmin : i ≤ j := moved.min'_le j hjmem
    exact (not_le_of_gt hji) hmin
  refine ⟨i, hprev, ?_⟩
  have hnotlt : ¬q i < Fin.castLEOrderEmb hpn i := by
    intro hqi
    let j : Fin p := ⟨(q i).val, by
      have : (q i).val < i.val := by
        change (q i).val < i.val at hqi
        exact hqi
      exact this.trans i.isLt⟩
    have hji : j < i := by
      change (q i).val < i.val
      change (q i).val < i.val at hqi
      exact hqi
    have hqj : q j = Fin.castLEOrderEmb hpn j := hprev j hji
    have hcast : Fin.castLEOrderEmb hpn j = q i := by
      apply Fin.ext
      rfl
    have hjiEq : j = i := q.injective (hqj.trans hcast)
    exact (ne_of_lt hji) hjiEq
  exact lt_of_le_of_ne (le_of_not_gt hnotlt) hiMoved.symm

/-- Exponent vector of the determinant term indexed by a permutation.  The
outer embedding gives the variable blocks and the inner embedding gives the
ordered variables within each block. -/
def blockPermutationExponent {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) : StandardAuxVar n m →₀ ℕ :=
  ∑ j, Finsupp.single (toLex (q j, a (u j))) 1

/-- The combined diagonal exponent of two determinants using the same outer
blocks (the `Y` and `Z` determinants in Cauchy--Binet). -/
def twoBlockDiagonalExponent {p n m : ℕ}
    (q : Fin p ↪o Fin n)
    (a b : Fin p ↪o (Fin n ⊕ₗ Fin m)) : StandardAuxVar n m →₀ ℕ :=
  blockPermutationExponent q a 1 + blockPermutationExponent q b 1

lemma finsupp_fintype_sum_apply {I α : Type*} [Fintype I]
    {M : Type*} [AddCommMonoid M] (f : I → α →₀ M) (x : α) :
    (∑ i, f i) x = ∑ i, f i x := by
  classical
  change (Finsupp.applyAddHom x) (∑ i, f i) = _
  rw [map_sum]
  simp only [Finsupp.applyAddHom_apply]

lemma blockPermutationExponent_apply_own {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) (k : Fin p) :
    blockPermutationExponent q a u (toLex (q k, a (u k))) = 1 := by
  classical
  rw [blockPermutationExponent]
  rw [finsupp_fintype_sum_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp only [Finsupp.single_apply]
    rw [if_neg]
    intro heq
    exact hjk (q.injective (congrArg (fun v ↦ (ofLex v).1) heq))
  · simp

lemma blockPermutationExponent_apply_same_outer {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (i : Fin p) (c : Fin n ⊕ₗ Fin m) :
    blockPermutationExponent q a 1 (toLex (q i, c)) =
      if a i = c then 1 else 0 := by
  classical
  rw [blockPermutationExponent, finsupp_fintype_sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [Finsupp.single_apply]
  · intro j hj hji
    simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
    rw [if_neg]
    intro heq
    exact hji (q.injective (congrArg (fun v ↦ (ofLex v).1) heq))
  · simp

lemma blockPermutationExponent_apply_of_outer_ne {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (r : Fin n) (c : Fin n ⊕ₗ Fin m) (hr : ∀ i, q i ≠ r) :
    blockPermutationExponent q a 1 (toLex (r, c)) = 0 := by
  classical
  rw [blockPermutationExponent, finsupp_fintype_sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
  rw [if_neg]
  intro heq
  exact hr i (congrArg (fun v ↦ (ofLex v).1) heq)

lemma blockPermutationExponent_apply_identity_zero_of_moved
    {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) (i : Fin p) (hui : u i ≠ i) :
    blockPermutationExponent q a u (toLex (q i, a i)) = 0 := by
  classical
  rw [blockPermutationExponent]
  rw [finsupp_fintype_sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finsupp.single_apply]
  rw [if_neg]
  intro heq
  have hji : j = i := q.injective (congrArg (fun v ↦ (ofLex v).1) heq)
  subst j
  have hai : a (u i) = a i := congrArg (fun v ↦ (ofLex v).2) heq
  exact hui (a.injective hai)

/-- In lexicographic order, the identity term of a generic determinant is
strictly larger than every other permutation term. -/
lemma blockPermutationExponent_lt_identity {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) (hu : u ≠ 1) :
    blockPermutationExponent q a u ≺[MonomialOrder.lex]
      blockPermutationExponent q a 1 := by
  classical
  obtain ⟨i, hprev, hiu⟩ := Equiv.Perm.exists_first_moved_up u hu
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨toLex (q i, a i), ?_, ?_⟩
  · intro v hv
    simp only [ofLex_toLex]
    rw [blockPermutationExponent, blockPermutationExponent,
      finsupp_fintype_sum_apply, finsupp_fintype_sum_apply]
    simp only [Equiv.Perm.one_apply]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j < i
    · rw [hprev j hji]
    · have hij : i ≤ j := le_of_not_gt hji
      have hneId : toLex (q j, a j) ≠ v := by
        intro heq
        rw [← heq] at hv
        simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
        rcases hv with hqji | ⟨hqji, haji⟩
        · exact (not_lt_of_ge hij) (q.lt_iff_lt.mp hqji)
        · have hji' : j = i := q.injective hqji
          subst j
          exact lt_irrefl _ haji
      have hneU : toLex (q j, a (u j)) ≠ v := by
        intro heq
        rw [← heq] at hv
        simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
        rcases hv with hqji | ⟨hqji, haui⟩
        · exact (not_lt_of_ge hij) (q.lt_iff_lt.mp hqji)
        · have hji' : j = i := q.injective hqji
          subst j
          exact (not_lt_of_ge (a.monotone hiu.le)) haui
      simp [Finsupp.single_apply, hneId, hneU]
  · change blockPermutationExponent q a u (toLex (q i, a i)) <
      blockPermutationExponent q a 1 (toLex (q i, a i))
    rw [blockPermutationExponent_apply_identity_zero_of_moved
      q a u i hiu.ne']
    have hval : blockPermutationExponent q a 1 (toLex (q i, a i)) = 1 := by
      simpa using blockPermutationExponent_apply_own q a
        (1 : Equiv.Perm (Fin p)) i
    rw [hval]
    norm_num

/-- Among increasing choices of outer blocks, the initial segment has the
unique largest combined diagonal exponent. -/
lemma twoBlockDiagonalExponent_lt_initial {p n m : ℕ} (hpn : p ≤ n)
    (q : Fin p ↪o Fin n) (a b : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (hab : ∀ i, a i < b i) (hq : q ≠ Fin.castLEOrderEmb hpn) :
    twoBlockDiagonalExponent q a b ≺[MonomialOrder.lex]
      twoBlockDiagonalExponent (Fin.castLEOrderEmb hpn) a b := by
  classical
  obtain ⟨i, hprev, hiq⟩ :=
    OrderEmbedding.Fin.exists_first_ne_castLE_up hpn q hq
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨toLex (Fin.castLEOrderEmb hpn i, a i), ?_, ?_⟩
  · intro v hv
    simp only [ofLex_toLex]
    rw [twoBlockDiagonalExponent, twoBlockDiagonalExponent,
      Finsupp.add_apply, Finsupp.add_apply,
      blockPermutationExponent, blockPermutationExponent,
      blockPermutationExponent, blockPermutationExponent]
    simp only [Equiv.Perm.one_apply, finsupp_fintype_sum_apply]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j < i
      · rw [hprev j hji]
      · have hij : i ≤ j := le_of_not_gt hji
        have hInitialNe :
            toLex (Fin.castLE hpn j, a j) ≠ v := by
          intro heq
          rw [← heq] at hv
          simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
          rcases hv with houter | ⟨houter, hinner⟩
          · exact (not_lt_of_ge hij) ((Fin.castLEOrderEmb hpn).lt_iff_lt.mp houter)
          · have hjiEq : j = i :=
              (Fin.castLEOrderEmb hpn).injective houter
            subst j
            exact lt_irrefl _ hinner
        have hActualNe : toLex (q j, a j) ≠ v := by
          intro heq
          rw [← heq] at hv
          simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
          rcases hv with houter | ⟨houter, hinner⟩
          · exact (not_lt_of_ge (hiq.le.trans (q.monotone hij))) houter
          · exact (ne_of_gt (hiq.trans_le (q.monotone hij))) houter
        simp [Finsupp.single_apply, hInitialNe, hActualNe]
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j < i
      · rw [hprev j hji]
      · have hij : i ≤ j := le_of_not_gt hji
        have hInitialNe :
            toLex (Fin.castLE hpn j, b j) ≠ v := by
          intro heq
          rw [← heq] at hv
          simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
          rcases hv with houter | ⟨houter, hinner⟩
          · exact (not_lt_of_ge hij) ((Fin.castLEOrderEmb hpn).lt_iff_lt.mp houter)
          · have hjiEq : j = i :=
              (Fin.castLEOrderEmb hpn).injective houter
            subst j
            exact (not_lt_of_ge (hab i).le) hinner
        have hActualNe : toLex (q j, b j) ≠ v := by
          intro heq
          rw [← heq] at hv
          simp only [Prod.Lex.lt_iff, ofLex_toLex] at hv
          rcases hv with houter | ⟨houter, hinner⟩
          · exact (not_lt_of_ge (hiq.le.trans (q.monotone hij))) houter
          · exact (ne_of_gt (hiq.trans_le (q.monotone hij))) houter
        simp [Finsupp.single_apply, hInitialNe, hActualNe]
  · simp only [ofLex_toLex]
    rw [twoBlockDiagonalExponent, twoBlockDiagonalExponent,
      Finsupp.add_apply, Finsupp.add_apply]
    have hActualA : blockPermutationExponent q a 1
        (toLex (Fin.castLEOrderEmb hpn i, a i)) = 0 := by
      rw [blockPermutationExponent, finsupp_fintype_sum_apply]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
      rw [if_neg]
      intro heq
      have houter : q j = Fin.castLEOrderEmb hpn i :=
        congrArg (fun x ↦ (ofLex x).1) heq
      by_cases hji : j < i
      · rw [hprev j hji] at houter
        exact (ne_of_lt hji) ((Fin.castLEOrderEmb hpn).injective houter)
      · exact (ne_of_gt (hiq.trans_le (q.monotone (le_of_not_gt hji)))) houter
    have hActualB : blockPermutationExponent q b 1
        (toLex (Fin.castLEOrderEmb hpn i, a i)) = 0 := by
      rw [blockPermutationExponent, finsupp_fintype_sum_apply]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
      rw [if_neg]
      intro heq
      have houter : q j = Fin.castLEOrderEmb hpn i :=
        congrArg (fun x ↦ (ofLex x).1) heq
      by_cases hji : j < i
      · rw [hprev j hji] at houter
        exact (ne_of_lt hji) ((Fin.castLEOrderEmb hpn).injective houter)
      · exact (ne_of_gt (hiq.trans_le (q.monotone (le_of_not_gt hji)))) houter
    have hInitialA : blockPermutationExponent (Fin.castLEOrderEmb hpn) a 1
        (toLex (Fin.castLEOrderEmb hpn i, a i)) = 1 := by
      simpa using blockPermutationExponent_apply_own
        (Fin.castLEOrderEmb hpn) a (1 : Equiv.Perm (Fin p)) i
    have hInitialB : blockPermutationExponent (Fin.castLEOrderEmb hpn) b 1
        (toLex (Fin.castLEOrderEmb hpn i, a i)) = 0 := by
      rw [blockPermutationExponent, finsupp_fintype_sum_apply]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Equiv.Perm.one_apply, Finsupp.single_apply]
      rw [if_neg]
      intro heq
      have houter : Fin.castLEOrderEmb hpn j = Fin.castLEOrderEmb hpn i :=
        congrArg (fun x ↦ (ofLex x).1) heq
      have hji : j = i := (Fin.castLEOrderEmb hpn).injective houter
      subst j
      have hinner : b i = a i := congrArg (fun x ↦ (ofLex x).2) heq
      exact (ne_of_gt (hab i)) hinner
    rw [hActualA, hActualB, hInitialA, hInitialB]
    norm_num

def FinsetMinorIndex.rowInnerOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) : Fin d.rows.card ↪o (Fin n ⊕ₗ Fin m) where
  toFun i := toLex (Sum.inl (d.rows.orderEmbOfFin rfl i))
  inj' := by
    intro i j hij
    have hsum := toLex.injective hij
    have hrow := Sum.inl_injective hsum
    exact (d.rows.orderEmbOfFin rfl).injective hrow
  map_rel_iff' := by
    intro i j
    change toLex (Sum.inl (d.rows.orderEmbOfFin rfl i) : Fin n ⊕ Fin m) ≤
      toLex (Sum.inl (d.rows.orderEmbOfFin rfl j) : Fin n ⊕ Fin m) ↔ i ≤ j
    simpa only [Sum.Lex.inl_le_inl_iff] using
      (d.rows.orderEmbOfFin rfl).le_iff_le

/-- Column variables indexed using the row cardinality of the minor. -/
def FinsetMinorIndex.colInnerFromRowsOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) :
    Fin d.rows.card ↪o (Fin n ⊕ₗ Fin m) where
  toFun i := toLex (Sum.inr (d.cols.orderEmbOfFin d.card_eq.symm i))
  inj' := by
    intro i j hij
    have hsum := toLex.injective hij
    have hcol := Sum.inr_injective hsum
    exact (d.cols.orderEmbOfFin d.card_eq.symm).injective hcol
  map_rel_iff' := by
    intro i j
    change toLex (Sum.inr
        (d.cols.orderEmbOfFin d.card_eq.symm i) : Fin n ⊕ Fin m) ≤
      toLex (Sum.inr
        (d.cols.orderEmbOfFin d.card_eq.symm j) : Fin n ⊕ Fin m) ↔ i ≤ j
    simpa only [Sum.Lex.inr_le_inr_iff] using
      (d.cols.orderEmbOfFin d.card_eq.symm).le_iff_le

-- port to Lean 4.33.1: `simp` no longer reduces these structure-literal embeddings when applied
@[simp] lemma FinsetMinorIndex.rowInnerOrderEmbedding_apply {n m : ℕ}
    (d : FinsetMinorIndex n m) (i : Fin d.rows.card) :
    d.rowInnerOrderEmbedding i = toLex (Sum.inl (d.rows.orderEmbOfFin rfl i)) := rfl

@[simp] lemma FinsetMinorIndex.colInnerFromRowsOrderEmbedding_apply {n m : ℕ}
    (d : FinsetMinorIndex n m) (i : Fin d.rows.card) :
    d.colInnerFromRowsOrderEmbedding i =
      toLex (Sum.inr (d.cols.orderEmbOfFin d.card_eq.symm i)) := rfl

lemma FinsetMinorIndex.rowInnerOrderEmbedding_lt_colInnerFromRowsOrderEmbedding
    {n m : ℕ} (d : FinsetMinorIndex n m) (i : Fin d.rows.card) :
    d.rowInnerOrderEmbedding i < d.colInnerFromRowsOrderEmbedding i := by
  exact Sum.Lex.inl_lt_inr _ _

/-- The order embedding of the initial inner-index set
`{0, ..., rows.card - 1}`. -/
def FinsetMinorIndex.initialInnerOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) : Fin d.rows.card ↪o Fin n :=
  Fin.castLEOrderEmb (by simpa using Finset.card_le_univ d.rows)

/-- Increasing enumeration of the image of an injective finite function. -/
def injectionRangeOrderEmbedding {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) : Fin p ↪o Fin n :=
  (Finset.univ.image f).orderEmbOfFin (by
    rw [Finset.card_image_of_injective _ hf]
    simp)

lemma injectionRangeOrderEmbedding_range {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) :
    Set.range (injectionRangeOrderEmbedding f hf) = Set.range f := by
  rw [injectionRangeOrderEmbedding, Finset.range_orderEmbOfFin]
  ext x
  simp

lemma exists_injectionRangeOrderEmbedding_eq {p n : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f) (i : Fin p) :
    ∃ j, injectionRangeOrderEmbedding f hf j = f i := by
  have hi : f i ∈ Set.range (injectionRangeOrderEmbedding f hf) := by
    rw [injectionRangeOrderEmbedding_range f hf]
    exact ⟨i, rfl⟩
  exact hi

/-- The index of `f i` in the increasing enumeration of the image of `f`. -/
def injectionSortingIndex {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) (i : Fin p) : Fin p :=
  Classical.choose (exists_injectionRangeOrderEmbedding_eq f hf i)

@[simp] lemma injectionRangeOrderEmbedding_sortingIndex {p n : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f) (i : Fin p) :
    injectionRangeOrderEmbedding f hf (injectionSortingIndex f hf i) = f i :=
  Classical.choose_spec (exists_injectionRangeOrderEmbedding_eq f hf i)

lemma injectionSortingIndex_injective {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) : Function.Injective (injectionSortingIndex f hf) := by
  intro i j hij
  apply hf
  rw [← injectionRangeOrderEmbedding_sortingIndex f hf i,
    ← injectionRangeOrderEmbedding_sortingIndex f hf j, hij]

/-- Permutation which records how an injective function differs from the
increasing enumeration of its image. -/
def injectionSortingPerm {p n : ℕ} (f : Fin p → Fin n)
    (hf : Function.Injective f) : Equiv.Perm (Fin p) :=
  Equiv.ofBijective (injectionSortingIndex f hf)
    ⟨injectionSortingIndex_injective f hf,
      Finite.injective_iff_surjective.mp
        (injectionSortingIndex_injective f hf)⟩

@[simp] lemma injectionRangeOrderEmbedding_sortingPerm {p n : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f) (i : Fin p) :
    injectionRangeOrderEmbedding f hf (injectionSortingPerm f hf i) = f i := by
  exact injectionRangeOrderEmbedding_sortingIndex f hf i

@[simp] lemma injectionRangeOrderEmbedding_of_orderEmbedding {p n : ℕ}
    (q : Fin p ↪o Fin n) :
    injectionRangeOrderEmbedding q q.injective = q := by
  rw [injectionRangeOrderEmbedding]
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  simp

@[simp] lemma injectionSortingPerm_of_orderEmbedding {p n : ℕ}
    (q : Fin p ↪o Fin n) :
    injectionSortingPerm q q.injective = 1 := by
  apply Equiv.ext
  intro i
  apply q.injective
  have hi := injectionRangeOrderEmbedding_sortingPerm
    (q : Fin p → Fin n) q.injective i
  simpa using hi

/-- Generic block matrix whose diagonal term is controlled by
`blockPermutationExponent`. -/
def blockGenericMatrix {D : Type*} [CommRing D] {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    Matrix (Fin p) (Fin p) (StandardAuxPoly D n m) :=
  fun i j ↦ MvPolynomial.X (toLex (q j, a i))

/-- Sorting the rows selected by an injective function changes the
corresponding block determinant only by the sign of the sorting
permutation. -/
lemma det_injectiveRows_eq_sign_mul_blockGenericMatrix
    {D : Type*} [CommRing D] {p n m : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f)
    (a : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    Matrix.det (fun i j : Fin p ↦
        (MvPolynomial.X (toLex (f i, a j)) : StandardAuxPoly D n m)) =
      (((injectionSortingPerm f hf).sign : ℤ) : StandardAuxPoly D n m) *
        Matrix.det (blockGenericMatrix (D := D)
          (injectionRangeOrderEmbedding f hf) a) := by
  let q := injectionRangeOrderEmbedding f hf
  let u := injectionSortingPerm f hf
  let A : Matrix (Fin p) (Fin p) (StandardAuxPoly D n m) :=
    fun i j ↦ MvPolynomial.X (toLex (f i, a j))
  let B : Matrix (Fin p) (Fin p) (StandardAuxPoly D n m) :=
    blockGenericMatrix (D := D) q a
  have htranspose : A.transpose = B.submatrix id u := by
    ext i j
    simp only [A, B, Matrix.transpose, Matrix.of_apply, Matrix.submatrix_apply,
      Function.id_def, blockGenericMatrix, q, u]
    rw [injectionRangeOrderEmbedding_sortingPerm]
  calc
    Matrix.det (fun i j : Fin p ↦
        (MvPolynomial.X (toLex (f i, a j)) : StandardAuxPoly D n m)) =
        Matrix.det A := rfl
    _ = Matrix.det A.transpose := (Matrix.det_transpose A).symm
    _ = Matrix.det (B.submatrix id u) := congrArg Matrix.det htranspose
    _ = (((u.sign : ℤ) : StandardAuxPoly D n m) * Matrix.det B) :=
      Matrix.det_permute' u B
    _ = _ := rfl

lemma blockGenericMatrix_det_term
    {D : Type*} [CommRing D] {p n m : ℕ}
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m))
    (u : Equiv.Perm (Fin p)) :
    (((u.sign : ℤ) : StandardAuxPoly D n m) *
        ∏ j, blockGenericMatrix (D := D) q a (u j) j) =
      MvPolynomial.monomial (blockPermutationExponent q a u)
        ((u.sign : ℤ) : D) := by
  classical
  have hmono := MvPolynomial.monomial_sum_index
    (R := D) (Finset.univ : Finset (Fin p))
    (fun j ↦ Finsupp.single (toLex (q j, a (u j))) 1)
    ((u.sign : ℤ) : D)
  symm
  rw [blockPermutationExponent]
  calc
    MvPolynomial.monomial
        (∑ j, Finsupp.single (toLex (q j, a (u j))) 1)
        ((u.sign : ℤ) : D) =
        MvPolynomial.C ((u.sign : ℤ) : D) *
          ∏ j, MvPolynomial.monomial
            (Finsupp.single (toLex (q j, a (u j))) 1) 1 := hmono
    _ = (((u.sign : ℤ) : StandardAuxPoly D n m) *
        ∏ j, blockGenericMatrix (D := D) q a (u j) j) := by
      simp [blockGenericMatrix, MvPolynomial.X]

/-- In a generic block determinant, the diagonal monomial is the unique
largest monomial for lexicographic order, and its coefficient is one. -/
lemma blockGenericMatrix_det_degree_monic
    {D : Type*} [CommRing D] [Nontrivial D] {p n m : ℕ} (hp : 0 < p)
    (q : Fin p ↪o Fin n) (a : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (Matrix.det (blockGenericMatrix (D := D) q a)) =
          blockPermutationExponent q a 1 ∧
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (Matrix.det (blockGenericMatrix (D := D) q a)) := by
  classical
  let term : Equiv.Perm (Fin p) → StandardAuxPoly D n m := fun u ↦
    ((u.sign : ℤ) : StandardAuxPoly D n m) *
      ∏ j, blockGenericMatrix (D := D) q a (u j) j
  have hterm (u : Equiv.Perm (Fin p)) :
      term u = MvPolynomial.monomial (blockPermutationExponent q a u)
        ((u.sign : ℤ) : D) :=
    blockGenericMatrix_det_term q a u
  have hid : term 1 =
      MvPolynomial.monomial (blockPermutationExponent q a 1) 1 := by
    rw [hterm]
    simp
  have he_ne : blockPermutationExponent q a 1 ≠ 0 := by
    let i : Fin p := ⟨0, hp⟩
    intro he
    have hvalue := blockPermutationExponent_apply_own q a
      (1 : Equiv.Perm (Fin p)) i
    rw [he] at hvalue
    simp at hvalue
  have he_pos :
      (0 : (MonomialOrder.lex : MonomialOrder
        (StandardAuxVar n m)).syn) <
        (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).toSyn (blockPermutationExponent q a 1) := by
    rw [MonomialOrder.toSyn_lt_iff_ne_zero]
    intro he
    exact he_ne ((MonomialOrder.toSyn_eq_zero_iff
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m))
      (blockPermutationExponent q a 1)).mp he)
  have hdet : Matrix.det (blockGenericMatrix (D := D) q a) =
      term 1 + ∑ u ∈ (Finset.univ.erase
        (1 : Equiv.Perm (Fin p))), term u := by
    rw [Matrix.det_apply']
    exact (Finset.add_sum_erase Finset.univ term
      (Finset.mem_univ (1 : Equiv.Perm (Fin p)))).symm
  have hrest :
      (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).toSyn
          ((MonomialOrder.lex : MonomialOrder
            (StandardAuxVar n m)).degree
            (∑ u ∈ (Finset.univ.erase
              (1 : Equiv.Perm (Fin p))), term u)) <
        (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).toSyn (blockPermutationExponent q a 1) := by
    refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
    rw [Finset.sup_lt_iff he_pos]
    intro u hu
    rw [hterm, MonomialOrder.degree_monomial]
    have hsign : ((u.sign : ℤ) : D) ≠ 0 := by
      rcases Int.units_eq_one_or u.sign with hs | hs <;> simp [hs]
    rw [if_neg hsign]
    exact blockPermutationExponent_lt_identity q a u
      (Finset.mem_erase.mp hu).1
  have hdiagDegree :
      (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).degree
          (MvPolynomial.monomial (blockPermutationExponent q a 1) (1 : D)) =
        blockPermutationExponent q a 1 := by
    simp [MonomialOrder.degree_monomial]
  rw [hdet, hid]
  constructor
  · calc
      (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).degree
          (MvPolynomial.monomial (blockPermutationExponent q a 1) (1 : D) +
            ∑ u ∈ (Finset.univ.erase
              (1 : Equiv.Perm (Fin p))), term u) =
          (MonomialOrder.lex : MonomialOrder
            (StandardAuxVar n m)).degree
            (MvPolynomial.monomial
              (blockPermutationExponent q a 1) (1 : D)) := by
            apply (MonomialOrder.lex : MonomialOrder
              (StandardAuxVar n m)).degree_add_of_lt
            simpa only [hdiagDegree] using hrest
      _ = blockPermutationExponent q a 1 := hdiagDegree
  · apply MonomialOrder.Monic.add_of_lt
      (m := (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)))
      MonomialOrder.monic_monomial_one
    simpa only [hdiagDegree] using hrest

/-- Exponent vector of the diagonal monomial attached to a list of minors.
The first summand records `Y` variables and the second records `Z` variables. -/
def standardDiagonalCode {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) : StandardAuxVar n m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun qc ↦
    match ofLex (ofLex qc).2 with
    | Sum.inl a => Multiset.count a (minorRowProfile l (ofLex qc).1.val)
    | Sum.inr b => Multiset.count b (minorColProfile l (ofLex qc).1.val)

@[simp] lemma standardDiagonalCode_row_apply {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (q : Fin n) (a : Fin n) :
    standardDiagonalCode l (standardAuxYVar q a) =
      Multiset.count a (minorRowProfile l q.val) := by
  simp [standardDiagonalCode, standardAuxYVar]

@[simp] lemma standardDiagonalCode_col_apply {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (q : Fin n) (b : Fin m) :
    standardDiagonalCode l (standardAuxZVar q b) =
      Multiset.count b (minorColProfile l q.val) := by
  simp [standardDiagonalCode, standardAuxZVar]

lemma initialTwoBlockDiagonalExponent_row_apply_of_lt {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (a : Fin n)
    (hq : q.val < d.rows.card) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (standardAuxYVar q a) =
      if d.rows.orderEmbOfFin rfl ⟨q.val, hq⟩ = a then 1 else 0 := by
  let i : Fin d.rows.card := ⟨q.val, hq⟩
  have hqi : d.initialInnerOrderEmbedding i = q := by
    apply Fin.ext
    rfl
  change twoBlockDiagonalExponent d.initialInnerOrderEmbedding
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
      (toLex (q, toLex (Sum.inl a))) =
        if d.rows.orderEmbOfFin rfl i = a then 1 else 0
  rw [← hqi, twoBlockDiagonalExponent, Finsupp.add_apply,
    blockPermutationExponent_apply_same_outer,
    blockPermutationExponent_apply_same_outer]
  simp [FinsetMinorIndex.rowInnerOrderEmbedding_apply,
    FinsetMinorIndex.colInnerFromRowsOrderEmbedding_apply, i]

lemma initialTwoBlockDiagonalExponent_row_apply_of_ge {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (a : Fin n)
    (hq : d.rows.card ≤ q.val) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (standardAuxYVar q a) = 0 := by
  have houter : ∀ i, d.initialInnerOrderEmbedding i ≠ q := by
    intro i hi
    have hval : i.val = q.val := congrArg Fin.val hi
    exact (not_lt_of_ge hq) (hval ▸ i.isLt)
  change twoBlockDiagonalExponent d.initialInnerOrderEmbedding
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
      (toLex (q, toLex (Sum.inl a))) = 0
  rw [twoBlockDiagonalExponent, Finsupp.add_apply,
    blockPermutationExponent_apply_of_outer_ne _ _ _ _ houter,
    blockPermutationExponent_apply_of_outer_ne _ _ _ _ houter,
    add_zero]

lemma initialTwoBlockDiagonalExponent_col_apply_of_lt {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (b : Fin m)
    (hq : q.val < d.rows.card) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (standardAuxZVar q b) =
      if d.cols.orderEmbOfFin d.card_eq.symm ⟨q.val, hq⟩ = b then 1 else 0 := by
  let i : Fin d.rows.card := ⟨q.val, hq⟩
  have hqi : d.initialInnerOrderEmbedding i = q := by
    apply Fin.ext
    rfl
  change twoBlockDiagonalExponent d.initialInnerOrderEmbedding
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
      (toLex (q, toLex (Sum.inr b))) =
        if d.cols.orderEmbOfFin d.card_eq.symm i = b then 1 else 0
  rw [← hqi, twoBlockDiagonalExponent, Finsupp.add_apply,
    blockPermutationExponent_apply_same_outer,
    blockPermutationExponent_apply_same_outer]
  simp [FinsetMinorIndex.rowInnerOrderEmbedding_apply,
    FinsetMinorIndex.colInnerFromRowsOrderEmbedding_apply, i]

lemma initialTwoBlockDiagonalExponent_col_apply_of_ge {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (b : Fin m)
    (hq : d.rows.card ≤ q.val) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (standardAuxZVar q b) = 0 := by
  have houter : ∀ i, d.initialInnerOrderEmbedding i ≠ q := by
    intro i hi
    have hval : i.val = q.val := congrArg Fin.val hi
    exact (not_lt_of_ge hq) (hval ▸ i.isLt)
  change twoBlockDiagonalExponent d.initialInnerOrderEmbedding
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
      (toLex (q, toLex (Sum.inr b))) = 0
  rw [twoBlockDiagonalExponent, Finsupp.add_apply,
    blockPermutationExponent_apply_of_outer_ne _ _ _ _ houter,
    blockPermutationExponent_apply_of_outer_ne _ _ _ _ houter,
    add_zero]

lemma standardDiagonalCode_singleton_row_apply_of_lt {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (a : Fin n)
    (hq : q.val < d.rows.card) :
    standardDiagonalCode [d] (standardAuxYVar q a) =
      if d.rows.orderEmbOfFin rfl ⟨q.val, hq⟩ = a then 1 else 0 := by
  rw [standardDiagonalCode_row_apply]
  change Multiset.count a (minorRowColumn [d] q.val : Multiset (Fin n)) = _
  rw [minorRowColumn]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [d.rowAt?_eq_some q.val hq]
  by_cases ha : d.rows.orderEmbOfFin rfl ⟨q.val, hq⟩ = a
  · simp [ha]
  · have ha' : a ≠ d.rows.orderEmbOfFin rfl ⟨q.val, hq⟩ := by
      exact fun h ↦ ha h.symm
    simp [ha, ha']

lemma standardDiagonalCode_singleton_row_apply_of_ge {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (a : Fin n)
    (hq : d.rows.card ≤ q.val) :
    standardDiagonalCode [d] (standardAuxYVar q a) = 0 := by
  rw [standardDiagonalCode_row_apply]
  simp [minorRowProfile, minorRowColumn, FinsetMinorIndex.rowAt?, hq]

lemma standardDiagonalCode_singleton_col_apply_of_lt {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (b : Fin m)
    (hq : q.val < d.rows.card) :
    standardDiagonalCode [d] (standardAuxZVar q b) =
      if d.cols.orderEmbOfFin d.card_eq.symm ⟨q.val, hq⟩ = b then 1 else 0 := by
  have hqc : q.val < d.cols.card := by
    rwa [← d.card_eq]
  rw [standardDiagonalCode_col_apply]
  change Multiset.count b (minorColColumn [d] q.val : Multiset (Fin m)) = _
  rw [minorColColumn]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [d.colAt?_eq_some q.val hqc]
  have hvalue : d.cols.orderEmbOfFin rfl ⟨q.val, hqc⟩ =
      d.cols.orderEmbOfFin d.card_eq.symm ⟨q.val, hq⟩ := by
    rw [Finset.orderEmbOfFin_eq_orderEmbOfFin_iff]
  by_cases hb : d.cols.orderEmbOfFin d.card_eq.symm ⟨q.val, hq⟩ = b
  · rw [hvalue, hb]
    simp
  · have hb' : b ≠ d.cols.orderEmbOfFin rfl ⟨q.val, hqc⟩ := by
      intro h
      apply hb
      rw [← hvalue]
      exact h.symm
    simp [hb, hb']

lemma standardDiagonalCode_singleton_col_apply_of_ge {n m : ℕ}
    (d : FinsetMinorIndex n m) (q : Fin n) (b : Fin m)
    (hq : d.rows.card ≤ q.val) :
    standardDiagonalCode [d] (standardAuxZVar q b) = 0 := by
  have hqc : d.cols.card ≤ q.val := by
    rwa [← d.card_eq]
  rw [standardDiagonalCode_col_apply]
  simp [minorColProfile, minorColColumn, FinsetMinorIndex.colAt?, hqc]

/-- The initial diagonal exponent computed from the two auxiliary
determinants is exactly the profile code of the singleton minor list. -/
lemma initialTwoBlockDiagonalExponent_eq_standardDiagonalCode_singleton
    {n m : ℕ} (d : FinsetMinorIndex n m) :
    twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding =
      standardDiagonalCode [d] := by
  apply Finsupp.ext
  intro qc
  let q : Fin n := (ofLex qc).1
  cases hinner : ofLex (ofLex qc).2 with
  | inl a =>
      have hqc : qc = standardAuxYVar q a := by
        calc
          qc = toLex (ofLex qc) := by simp
          _ = toLex (q, toLex (Sum.inl a)) := by
            apply congrArg (fun x : Fin n × (Fin n ⊕ₗ Fin m) ↦ toLex x)
            apply Prod.ext
            · rfl
            · apply toLex.injective
              exact hinner
      rw [hqc]
      by_cases hqrow : q.val < d.rows.card
      · rw [initialTwoBlockDiagonalExponent_row_apply_of_lt d q a hqrow,
          standardDiagonalCode_singleton_row_apply_of_lt d q a hqrow]
      · have hqrow' : d.rows.card ≤ q.val := Nat.le_of_not_gt hqrow
        rw [initialTwoBlockDiagonalExponent_row_apply_of_ge d q a hqrow',
          standardDiagonalCode_singleton_row_apply_of_ge d q a hqrow']
  | inr b =>
      have hqc : qc = standardAuxZVar q b := by
        calc
          qc = toLex (ofLex qc) := by simp
          _ = toLex (q, toLex (Sum.inr b)) := by
            apply congrArg (fun x : Fin n × (Fin n ⊕ₗ Fin m) ↦ toLex x)
            apply Prod.ext
            · rfl
            · apply toLex.injective
              exact hinner
      rw [hqc]
      by_cases hqrow : q.val < d.rows.card
      · rw [initialTwoBlockDiagonalExponent_col_apply_of_lt d q b hqrow,
          standardDiagonalCode_singleton_col_apply_of_lt d q b hqrow]
      · have hqrow' : d.rows.card ≤ q.val := Nat.le_of_not_gt hqrow
        rw [initialTwoBlockDiagonalExponent_col_apply_of_ge d q b hqrow',
          standardDiagonalCode_singleton_col_apply_of_ge d q b hqrow']

lemma standardDiagonalCode_cons {n m : ℕ} (d : FinsetMinorIndex n m)
    (l : List (FinsetMinorIndex n m)) :
    standardDiagonalCode (d :: l) =
      standardDiagonalCode [d] + standardDiagonalCode l := by
  apply Finsupp.ext
  intro qc
  cases hinner : ofLex (ofLex qc).2 with
  | inl a =>
      simp [standardDiagonalCode, minorRowProfile, minorRowColumn,
        minorColProfile, minorColColumn, hinner]
      cases hopt : d.rowAt? (ofLex qc).1.val with
      | none => simp [hopt]
      | some x =>
          by_cases hx : x = a <;> simp [hopt, hx, Nat.add_comm]
  | inr b =>
      simp [standardDiagonalCode, minorRowProfile, minorRowColumn,
        minorColProfile, minorColColumn, hinner]
      cases hopt : d.colAt? (ofLex qc).1.val with
      | none => simp [hopt]
      | some x =>
          by_cases hx : x = b <;> simp [hopt, hx, Nat.add_comm]

@[simp] lemma standardDiagonalCode_nil {n m : ℕ} :
    standardDiagonalCode ([] : List (FinsetMinorIndex n m)) = 0 := by
  apply Finsupp.ext
  intro qc
  cases hinner : ofLex (ofLex qc).2 <;>
    simp [standardDiagonalCode, minorRowProfile, minorRowColumn,
      minorColProfile, minorColColumn, hinner]

lemma minorRowColumn_eq_nil_of_n_le {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) {q : ℕ} (hq : n ≤ q) :
    minorRowColumn l q = [] := by
  rw [minorRowColumn, List.filterMap_eq_nil_iff]
  intro d hd
  have hcard : d.rows.card ≤ n := by
    simpa using Finset.card_le_univ d.rows
  exact d.rowAt?_eq_none q (hcard.trans hq)

lemma minorColColumn_eq_nil_of_n_le {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) {q : ℕ} (hq : n ≤ q) :
    minorColColumn l q = [] := by
  rw [minorColColumn, List.filterMap_eq_nil_iff]
  intro d hd
  apply d.colAt?_eq_none q
  calc
    d.cols.card = d.rows.card := d.card_eq.symm
    _ ≤ n := by simpa using Finset.card_le_univ d.rows
    _ ≤ q := hq

lemma rowProfile_eq_of_standardDiagonalCode_eq {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hcode : standardDiagonalCode l₁ = standardDiagonalCode l₂) :
    minorRowProfile l₁ = minorRowProfile l₂ := by
  funext q
  apply Multiset.ext.mpr
  intro a
  by_cases hq : q < n
  · let qn : Fin n := ⟨q, hq⟩
    have h := congrArg (fun c ↦ c (standardAuxYVar qn a)) hcode
    simpa using h
  · have hnq : n ≤ q := Nat.le_of_not_gt hq
    change Multiset.count a (minorRowColumn l₁ q : Multiset (Fin n)) =
      Multiset.count a (minorRowColumn l₂ q : Multiset (Fin n))
    rw [minorRowColumn_eq_nil_of_n_le l₁ hnq,
      minorRowColumn_eq_nil_of_n_le l₂ hnq]

lemma colProfile_eq_of_standardDiagonalCode_eq {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hcode : standardDiagonalCode l₁ = standardDiagonalCode l₂) :
    minorColProfile l₁ = minorColProfile l₂ := by
  funext q
  apply Multiset.ext.mpr
  intro b
  by_cases hq : q < n
  · let qn : Fin n := ⟨q, hq⟩
    have h := congrArg (fun c ↦ c (standardAuxZVar qn b)) hcode
    simpa using h
  · have hnq : n ≤ q := Nat.le_of_not_gt hq
    change Multiset.count b (minorColColumn l₁ q : Multiset (Fin m)) =
      Multiset.count b (minorColColumn l₂ q : Multiset (Fin m))
    rw [minorColColumn_eq_nil_of_n_le l₁ hnq,
      minorColColumn_eq_nil_of_n_le l₂ hnq]

/-- The diagonal exponent code is injective on standard products of nonempty
minors.  This is the recovery lemma used in the leading-term proof. -/
theorem standardDiagonalCode_injective_on_standard {n m : ℕ}
    {l₁ l₂ : List (FinsetMinorIndex n m)}
    (hl₁ : IsStandardMinorList l₁) (hl₂ : IsStandardMinorList l₂)
    (hne₁ : HasNoEmptyMinors l₁) (hne₂ : HasNoEmptyMinors l₂)
    (hcode : standardDiagonalCode l₁ = standardDiagonalCode l₂) :
    l₁ = l₂ :=
  eq_of_standard_minor_profiles hl₁ hl₂ hne₁ hne₂
    (rowProfile_eq_of_standardDiagonalCode_eq hcode)
    (colProfile_eq_of_standardDiagonalCode_eq hcode)

/-! ## The `X ↦ YZ` substitution -/

def auxY {D : Type*} [CommSemiring D] {n m : ℕ}
    (i q : Fin n) : StandardAuxPoly D n m :=
  MvPolynomial.X (standardAuxYVar q i)

def auxZ {D : Type*} [CommSemiring D] {n m : ℕ}
    (q : Fin n) (j : Fin m) : StandardAuxPoly D n m :=
  MvPolynomial.X (standardAuxZVar q j)

/-- Entry of the product of the auxiliary generic matrices `Y` and `Z`. -/
def auxYZEntry {D : Type*} [CommSemiring D] {n m : ℕ}
    (i : Fin n) (j : Fin m) : StandardAuxPoly D n m :=
  ∑ q : Fin n, auxY (D := D) i q * auxZ (D := D) q j

/-- The coefficient-preserving substitution from the generic matrix `X` to
the product of the auxiliary matrices `Y Z`. -/
def standardYZHom (D : Type*) [CommSemiring D] (n m : ℕ) :
    GenericPoly D n m →ₐ[D] StandardAuxPoly D n m :=
  MvPolynomial.bind₁ fun ij ↦ auxYZEntry (D := D) ij.1 ij.2

@[simp] lemma standardYZHom_X {D : Type*} [CommSemiring D] {n m : ℕ}
    (i : Fin n) (j : Fin m) :
    standardYZHom D n m (MvPolynomial.X (i, j)) =
      auxYZEntry (D := D) i j := by
  simp [standardYZHom]

lemma standardYZHom_minorPoly
    {D : Type*} [CommRing D] {n m : ℕ} (d : MinorIndex n m) :
    standardYZHom D n m (minorPoly d) =
      Matrix.det (fun a b : Fin d.size.val ↦
        auxYZEntry (D := D) (d.rows a) (d.cols b)) := by
  let N : Matrix (Fin d.size.val) (Fin d.size.val)
      (StandardAuxPoly D n m) :=
    fun a b ↦ auxYZEntry (D := D) (d.rows a) (d.cols b)
  change standardYZHom D n m (Matrix.det (minorMatrix d)) = Matrix.det N
  calc
    standardYZHom D n m (Matrix.det (minorMatrix d)) =
        Matrix.det ((standardYZHom D n m).toRingHom.mapMatrix
          (minorMatrix d)) :=
      (standardYZHom D n m).toRingHom.map_det (minorMatrix d)
    _ = Matrix.det N := by
      congr 1
      ext a b
      simp [N, minorMatrix]

/-- Under `X ↦ YZ`, a finite-set minor becomes the determinant of the
corresponding submatrix of `YZ`. -/
lemma standardYZHom_finsetMinorIndex_poly
    {D : Type*} [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m) :
    standardYZHom D n m d.poly =
      Matrix.det (fun a b : Fin d.rows.card ↦
        auxYZEntry (D := D)
          (d.rows.orderEmbOfFin rfl a)
          (d.cols.orderEmbOfFin d.card_eq.symm b)) := by
  unfold FinsetMinorIndex.poly
  rw [finsetMinorPoly_of_card_eq (hcard := d.card_eq)]
  rw [standardYZHom_minorPoly]
  rfl

/-- Row-multilinear expansion of the preceding determinant.  Terms are
indexed by all choices of an inner index; noninjective choices will vanish by
alternation in the next stage of the leading-term proof. -/
lemma standardYZHom_finsetMinorIndex_poly_expansion
    {D : Type*} [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m) :
    standardYZHom D n m d.poly =
      ∑ f : Fin d.rows.card → Fin n,
        (∏ i, auxY (D := D) (d.rows.orderEmbOfFin rfl i) (f i)) *
          Matrix.det (fun i j : Fin d.rows.card ↦
            auxZ (D := D) (f i)
              (d.cols.orderEmbOfFin d.card_eq.symm j)) := by
  rw [standardYZHom_finsetMinorIndex_poly]
  let y : Fin d.rows.card → Fin n → StandardAuxPoly D n m :=
    fun i q ↦ auxY (D := D) (d.rows.orderEmbOfFin rfl i) q
  let zrow : Fin n → Fin d.rows.card → StandardAuxPoly D n m :=
    fun q j ↦ auxZ (D := D) q
      (d.cols.orderEmbOfFin d.card_eq.symm j)
  change Matrix.det (fun i j ↦ ∑ q, y i q * zrow q j) = _
  change Matrix.detRowAlternating
      (fun i j ↦ ∑ q, y i q * zrow q j) = _
  calc
    Matrix.detRowAlternating (fun i j ↦ ∑ q, y i q * zrow q j) =
        ∑ f : Fin d.rows.card → Fin n,
          Matrix.detRowAlternating (fun i j ↦ y i (f i) * zrow (f i) j) := by
      have hmap := Matrix.detRowAlternating.toMultilinearMap.map_sum
        (g := fun i q j ↦ y i q * zrow q j)
      have hrows :
          (fun i j ↦ ∑ q, y i q * zrow q j) =
            (fun i ↦ ∑ q, (fun j ↦ y i q * zrow q j)) := by
        funext i j
        simp
      rw [hrows]
      exact hmap
    _ = ∑ f : Fin d.rows.card → Fin n,
        (∏ i, y i (f i)) * Matrix.det (fun i j ↦ zrow (f i) j) := by
      apply Finset.sum_congr rfl
      intro f hf
      change Matrix.detRowAlternating
          (fun i ↦ y i (f i) • zrow (f i)) = _
      rw [Matrix.detRowAlternating.map_smul_univ]
      rfl
    _ = _ := by rfl

lemma prod_X_eq_monomial_fintype
    {D : Type*} [CommSemiring D] {ι σ : Type*} [Fintype ι]
    (x : ι → σ) :
    (∏ i, MvPolynomial.X (x i) : MvPolynomial σ D) =
      MvPolynomial.monomial (∑ i, Finsupp.single (x i) 1) 1 := by
  classical
  symm
  have h := MvPolynomial.monomial_sum_index
    (R := D) (Finset.univ : Finset ι)
    (fun i ↦ Finsupp.single (x i) 1) (1 : D)
  simpa [MvPolynomial.X] using h

/-- The product of `X` variables selected by an injective function has the
permutation exponent obtained by sorting the image of that function. -/
lemma prod_X_injective_eq_monomial
    {D : Type*} [CommSemiring D] {p n m : ℕ}
    (f : Fin p → Fin n) (hf : Function.Injective f)
    (a : Fin p ↪o (Fin n ⊕ₗ Fin m)) :
    (∏ i, MvPolynomial.X (toLex (f i, a i)) : StandardAuxPoly D n m) =
      MvPolynomial.monomial
        (blockPermutationExponent (injectionRangeOrderEmbedding f hf) a
          (injectionSortingPerm f hf).symm) 1 := by
  classical
  let q := injectionRangeOrderEmbedding f hf
  let u := injectionSortingPerm f hf
  calc
    (∏ i, MvPolynomial.X (toLex (f i, a i)) : StandardAuxPoly D n m) =
        ∏ i, MvPolynomial.X (toLex (q (u i), a i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [injectionRangeOrderEmbedding_sortingPerm]
    _ = ∏ j, MvPolynomial.X (toLex (q j, a (u.symm j))) := by
      simpa only [u.symm_apply_apply] using
        (Equiv.prod_comp u (fun j ↦
          (MvPolynomial.X (toLex (q j, a (u.symm j))) :
            StandardAuxPoly D n m)))
    _ = MvPolynomial.monomial
        (blockPermutationExponent q a u.symm) 1 := by
      rw [blockPermutationExponent]
      exact prod_X_eq_monomial_fintype
        (D := D) (fun j ↦ toLex (q j, a (u.symm j)))
    _ = _ := rfl

lemma prod_auxY_injective_eq_monomial
    {D : Type*} [CommSemiring D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (f : Fin d.rows.card → Fin n)
    (hf : Function.Injective f) :
    (∏ i, auxY (D := D) (d.rows.orderEmbOfFin rfl i) (f i)) =
      MvPolynomial.monomial
        (blockPermutationExponent (injectionRangeOrderEmbedding f hf)
          d.rowInnerOrderEmbedding (injectionSortingPerm f hf).symm) 1 := by
  simpa [auxY, standardAuxYVar,
    FinsetMinorIndex.rowInnerOrderEmbedding_apply] using
    (prod_X_injective_eq_monomial (D := D) f hf
      d.rowInnerOrderEmbedding)

lemma det_auxZ_injective_eq_sign_mul_blockGenericMatrix
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (f : Fin d.rows.card → Fin n)
    (hf : Function.Injective f) :
    Matrix.det (fun i j : Fin d.rows.card ↦
        auxZ (D := D) (f i)
          (d.cols.orderEmbOfFin d.card_eq.symm j)) =
      (((injectionSortingPerm f hf).sign : ℤ) : StandardAuxPoly D n m) *
        Matrix.det (blockGenericMatrix (D := D)
          (injectionRangeOrderEmbedding f hf)
          d.colInnerFromRowsOrderEmbedding) := by
  simpa [auxZ, standardAuxZVar,
    FinsetMinorIndex.colInnerFromRowsOrderEmbedding_apply] using
    (det_injectiveRows_eq_sign_mul_blockGenericMatrix
      (D := D) f hf d.colInnerFromRowsOrderEmbedding)

/-- The summand indexed by an inner-index choice in the multilinear
expansion of a minor after `X ↦ YZ`. -/
def minorExpansionTerm
    (D : Type*) [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m)
    (f : Fin d.rows.card → Fin n) : StandardAuxPoly D n m :=
  (∏ i, auxY (D := D) (d.rows.orderEmbOfFin rfl i) (f i)) *
    Matrix.det (fun i j : Fin d.rows.card ↦
      auxZ (D := D) (f i)
        (d.cols.orderEmbOfFin d.card_eq.symm j))

/-- Exact leading exponent of an injective summand.  Sorting the chosen
inner indices produces the first determinant exponent; the second determinant
uses the increasing enumeration of the same image. -/
lemma minorExpansionTerm_degree_of_injective
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card)
    (f : Fin d.rows.card → Fin n) (hf : Function.Injective f) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (minorExpansionTerm D d f) =
      blockPermutationExponent (injectionRangeOrderEmbedding f hf)
          d.rowInnerOrderEmbedding (injectionSortingPerm f hf).symm +
        blockPermutationExponent (injectionRangeOrderEmbedding f hf)
          d.colInnerFromRowsOrderEmbedding 1 := by
  classical
  let q := injectionRangeOrderEmbedding f hf
  let u := injectionSortingPerm f hf
  let a := d.rowInnerOrderEmbedding
  let b := d.colInnerFromRowsOrderEmbedding
  have hy := prod_auxY_injective_eq_monomial (D := D) d f hf
  have hz := det_auxZ_injective_eq_sign_mul_blockGenericMatrix
    (D := D) d f hf
  have hb := blockGenericMatrix_det_degree_monic
    (D := D) hd q b
  have hscaledDegree :
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
          ((((u.sign : ℤ) : StandardAuxPoly D n m) *
            Matrix.det (blockGenericMatrix (D := D) q b))) =
        blockPermutationExponent q b 1 := by
    rcases Int.units_eq_one_or u.sign with hs | hs
    · simp [hs, hb.1]
    · simp [hs, hb.1]
  have hscaledLeadingCoeff :
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).leadingCoeff
          ((((u.sign : ℤ) : StandardAuxPoly D n m) *
            Matrix.det (blockGenericMatrix (D := D) q b))) ≠ 0 := by
    rcases Int.units_eq_one_or u.sign with hs | hs
    · simp [hs, hb.2.leadingCoeff_eq_one]
    · simp [hs, hb.2.leadingCoeff_eq_one]
  rw [minorExpansionTerm, hy, hz]
  rw [(MonomialOrder.lex : MonomialOrder
    (StandardAuxVar n m)).degree_mul_of_mul_leadingCoeff_ne_zero]
  · rw [MonomialOrder.degree_monomial, if_neg one_ne_zero,
      hscaledDegree]
  · rw [MonomialOrder.monic_monomial_one.leadingCoeff_eq_one, one_mul]
    exact hscaledLeadingCoeff

/-- Every injective summand other than the initial increasing choice has
strictly smaller degree than the initial diagonal exponent. -/
lemma minorExpansionTerm_degree_lt_initial_of_ne
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card)
    (f : Fin d.rows.card → Fin n) (hf : Function.Injective f)
    (hne : f ≠ d.initialInnerOrderEmbedding) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (minorExpansionTerm D d f) ≺[MonomialOrder.lex]
      twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding := by
  let q := injectionRangeOrderEmbedding f hf
  let u := injectionSortingPerm f hf
  have hdegree := minorExpansionTerm_degree_of_injective
    (D := D) d hd f hf
  rw [hdegree]
  have hperm (hu : u.symm ≠ 1) :
      blockPermutationExponent q d.rowInnerOrderEmbedding u.symm +
          blockPermutationExponent q d.colInnerFromRowsOrderEmbedding 1 ≺[MonomialOrder.lex]
        twoBlockDiagonalExponent q d.rowInnerOrderEmbedding
          d.colInnerFromRowsOrderEmbedding := by
    have h := add_lt_add_right
      (blockPermutationExponent_lt_identity q
        d.rowInnerOrderEmbedding u.symm hu)
      ((MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).toSyn
        (blockPermutationExponent q d.colInnerFromRowsOrderEmbedding 1))
    simpa [twoBlockDiagonalExponent] using h
  by_cases hq : q = d.initialInnerOrderEmbedding
  · have hu : u.symm ≠ 1 := by
      intro hu
      have huone : u = 1 := by
        apply Equiv.ext
        intro i
        have hi := DFunLike.congr_fun hu (u i)
        simpa using hi.symm
      apply hne
      funext i
      calc
        f i = q (u i) :=
          (injectionRangeOrderEmbedding_sortingPerm f hf i).symm
        _ = d.initialInnerOrderEmbedding i := by rw [hq, huone]; rfl
    simpa [q, u, hq] using hperm hu
  · have hqdiag :
        twoBlockDiagonalExponent q d.rowInnerOrderEmbedding
            d.colInnerFromRowsOrderEmbedding ≺[MonomialOrder.lex]
          twoBlockDiagonalExponent d.initialInnerOrderEmbedding
            d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding := by
      exact GenericMaximalMinor.twoBlockDiagonalExponent_lt_initial
        (p := d.rows.card) (n := n) (m := m)
        (by simpa using Finset.card_le_univ d.rows) q
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
        (fun i ↦ d.rowInnerOrderEmbedding_lt_colInnerFromRowsOrderEmbedding i)
        (by simpa [q, FinsetMinorIndex.initialInnerOrderEmbedding] using hq)
    by_cases hu : u.symm = 1
    · simpa [q, u, twoBlockDiagonalExponent, hu] using hqdiag
    · simpa [q, u] using lt_trans (hperm hu) hqdiag

lemma minorExpansionTerm_initial_eq
    {D : Type*} [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m) :
    minorExpansionTerm D d d.initialInnerOrderEmbedding =
      MvPolynomial.monomial
          (blockPermutationExponent d.initialInnerOrderEmbedding
            d.rowInnerOrderEmbedding 1) 1 *
        Matrix.det (blockGenericMatrix (D := D)
          d.initialInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding) := by
  have hy := prod_auxY_injective_eq_monomial (D := D) d
    d.initialInnerOrderEmbedding d.initialInnerOrderEmbedding.injective
  have hz := det_auxZ_injective_eq_sign_mul_blockGenericMatrix
    (D := D) d d.initialInnerOrderEmbedding
      d.initialInnerOrderEmbedding.injective
  rw [minorExpansionTerm, hy, hz]
  simp
  have hone : (1 : Equiv.Perm (Fin d.rows.card)).symm = 1 := by
    ext i
    rfl
  rw [hone]

/-- The initial summand is monic and has exactly the initial diagonal
exponent. -/
lemma minorExpansionTerm_initial_degree_monic
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (minorExpansionTerm D d d.initialInnerOrderEmbedding) =
      twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding ∧
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (minorExpansionTerm D d d.initialInnerOrderEmbedding) := by
  have hdegree := minorExpansionTerm_degree_of_injective
    (D := D) d hd d.initialInnerOrderEmbedding
      d.initialInnerOrderEmbedding.injective
  have hb := blockGenericMatrix_det_degree_monic (D := D) hd
    d.initialInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding
  constructor
  · have hone : (1 : Equiv.Perm (Fin d.rows.card)).symm = 1 := by
      ext i
      rfl
    simp only [injectionRangeOrderEmbedding_of_orderEmbedding,
      injectionSortingPerm_of_orderEmbedding] at hdegree
    rw [hone] at hdegree
    simpa only [twoBlockDiagonalExponent] using hdegree
  · rw [minorExpansionTerm_initial_eq]
    exact MonomialOrder.monic_monomial_one.mul hb.2

lemma auxZ_det_eq_zero_of_not_injective
    {D : Type*} [CommRing D] {n m p : ℕ}
    (f : Fin p → Fin n) (c : Fin p → Fin m)
    (hf : ¬Function.Injective f) :
    Matrix.det (fun i j ↦ auxZ (D := D) (f i) (c j)) = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_row_eq hne
  funext k
  rw [hij]

/-- The row expansion may be restricted to injective choices of inner
indices; every noninjective choice repeats a row of the `Z` determinant. -/
lemma standardYZHom_finsetMinorIndex_poly_injective_expansion
    {D : Type*} [CommRing D] {n m : ℕ} (d : FinsetMinorIndex n m) :
    standardYZHom D n m d.poly =
      ∑ f ∈ (Finset.univ.filter fun f : Fin d.rows.card → Fin n ↦
          Function.Injective f),
        (∏ i, auxY (D := D) (d.rows.orderEmbOfFin rfl i) (f i)) *
          Matrix.det (fun i j : Fin d.rows.card ↦
            auxZ (D := D) (f i)
              (d.cols.orderEmbOfFin d.card_eq.symm j)) := by
  rw [standardYZHom_finsetMinorIndex_poly_expansion]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro f hf hnotmem
  have hinj : ¬Function.Injective f := by
    intro hinj
    exact hnotmem (Finset.mem_filter.mpr ⟨hf, hinj⟩)
  have hz : Matrix.det (fun i j : Fin d.rows.card ↦
      auxZ (D := D) (f i)
        (d.cols.orderEmbOfFin d.card_eq.symm j)) = 0 :=
    auxZ_det_eq_zero_of_not_injective f
      (d.cols.orderEmbOfFin d.card_eq.symm) hinj
  rw [hz, mul_zero]

/-- A nonempty minor has the expected initial diagonal exponent after the
`X ↦ YZ` substitution, with leading coefficient one. -/
lemma standardYZHom_finsetMinorIndex_poly_degree_monic_of_nonempty
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (standardYZHom D n m d.poly) =
      twoBlockDiagonalExponent d.initialInnerOrderEmbedding
        d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding ∧
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (standardYZHom D n m d.poly) := by
  classical
  let q₀ := d.initialInnerOrderEmbedding
  let s : Finset (Fin d.rows.card → Fin n) :=
    Finset.univ.filter Function.Injective
  let principal := minorExpansionTerm D d q₀
  let rest := ∑ f ∈ s.erase q₀, minorExpansionTerm D d f
  have hq₀mem : (q₀ : Fin d.rows.card → Fin n) ∈ s := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q₀.injective⟩
  have hexpansion : standardYZHom D n m d.poly =
      ∑ f ∈ s, minorExpansionTerm D d f := by
    simpa [s, minorExpansionTerm] using
      (standardYZHom_finsetMinorIndex_poly_injective_expansion
        (D := D) d)
  have hdecomp : standardYZHom D n m d.poly = principal + rest := by
    rw [hexpansion]
    exact (Finset.add_sum_erase s (minorExpansionTerm D d) hq₀mem).symm
  have hprincipal := minorExpansionTerm_initial_degree_monic
    (D := D) d hd
  have hcode_ne : twoBlockDiagonalExponent q₀
      d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding ≠ 0 := by
    let i : Fin d.rows.card := ⟨0, hd⟩
    intro he
    have happ := congrArg (fun e ↦
      e (toLex (q₀ i, d.rowInnerOrderEmbedding i))) he
    have hrow : blockPermutationExponent q₀ d.rowInnerOrderEmbedding 1
        (toLex (q₀ i, d.rowInnerOrderEmbedding i)) = 1 := by
      simpa using blockPermutationExponent_apply_own q₀
        d.rowInnerOrderEmbedding (1 : Equiv.Perm (Fin d.rows.card)) i
    rw [twoBlockDiagonalExponent, Finsupp.add_apply, hrow] at happ
    simp at happ
  have hcode_pos :
      (0 : (MonomialOrder.lex : MonomialOrder
        (StandardAuxVar n m)).syn) <
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).toSyn
        (twoBlockDiagonalExponent q₀ d.rowInnerOrderEmbedding
          d.colInnerFromRowsOrderEmbedding) := by
    rw [MonomialOrder.toSyn_lt_iff_ne_zero]
    intro he
    exact hcode_ne ((MonomialOrder.toSyn_eq_zero_iff
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m))
      (twoBlockDiagonalExponent q₀ d.rowInnerOrderEmbedding
        d.colInnerFromRowsOrderEmbedding)).mp he)
  have hrest :
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree rest ≺[MonomialOrder.lex]
      twoBlockDiagonalExponent q₀ d.rowInnerOrderEmbedding
        d.colInnerFromRowsOrderEmbedding := by
    refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
    rw [Finset.sup_lt_iff hcode_pos]
    intro f hfmem
    have hfmem' : f ∈ s := (Finset.mem_erase.mp hfmem).2
    have hf : Function.Injective f := (Finset.mem_filter.mp hfmem').2
    have hfne : f ≠ q₀ := (Finset.mem_erase.mp hfmem).1
    simpa [q₀] using
      (minorExpansionTerm_degree_lt_initial_of_ne
        (D := D) d hd f hf hfne)
  rw [hdecomp]
  constructor
  · calc
      (MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).degree (principal + rest) =
          (MonomialOrder.lex : MonomialOrder
            (StandardAuxVar n m)).degree principal := by
            apply (MonomialOrder.lex : MonomialOrder
              (StandardAuxVar n m)).degree_add_of_lt
            simpa [principal, q₀, hprincipal.1] using hrest
      _ = twoBlockDiagonalExponent d.initialInnerOrderEmbedding
          d.rowInnerOrderEmbedding d.colInnerFromRowsOrderEmbedding := by
        simpa [principal, q₀] using hprincipal.1
  · apply MonomialOrder.Monic.add_of_lt
      (m := (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)))
    · simpa [principal, q₀] using hprincipal.2
    · simpa [principal, q₀, hprincipal.1] using hrest

/-- Paper-facing single-minor leading-term theorem, expressed using the
profile code employed by the recovery argument. -/
lemma standardYZHom_finsetMinorIndex_poly_degree_code_monic
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : 0 < d.rows.card) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (standardYZHom D n m d.poly) = standardDiagonalCode [d] ∧
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (standardYZHom D n m d.poly) := by
  have h := standardYZHom_finsetMinorIndex_poly_degree_monic_of_nonempty
    (D := D) d hd
  constructor
  · exact h.1.trans
      (initialTwoBlockDiagonalExponent_eq_standardDiagonalCode_singleton d)
  · exact h.2

/-- Every product of nonempty minors becomes a monic polynomial with degree
equal to its full diagonal profile code after `X ↦ YZ`. -/
theorem standardYZHom_minorListPoly_degree_code_monic
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) (hne : HasNoEmptyMinors l) :
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).degree
        (standardYZHom D n m (minorListPoly (D := D) l)) =
          standardDiagonalCode l ∧
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)).Monic
        (standardYZHom D n m (minorListPoly (D := D) l)) := by
  induction l with
  | nil =>
      simp [MonomialOrder.Monic, MonomialOrder.leadingCoeff]
  | cons d l ih =>
      have hd : 0 < d.rows.card :=
        Finset.card_pos.mpr (hne d (by simp))
      have htail : HasNoEmptyMinors l := by
        intro e he
        exact hne e (by simp [he])
      have hsingle :=
        standardYZHom_finsetMinorIndex_poly_degree_code_monic
          (D := D) d hd
      have hrest := ih htail
      rw [minorListPoly_cons, map_mul]
      constructor
      · rw [(MonomialOrder.lex : MonomialOrder
          (StandardAuxVar n m)).degree_mul_of_mul_leadingCoeff_ne_zero]
        · rw [hsingle.1, hrest.1]
          exact (standardDiagonalCode_cons d l).symm
        · rw [hsingle.2.leadingCoeff_eq_one,
            hrest.2.leadingCoeff_eq_one]
          simpa using (one_ne_zero : (1 : D) ≠ 0)
      · exact hsingle.2.mul hrest.2

/-! ## Linear independence of standard products -/

/-- A family of multivariate polynomials with pairwise distinct monic leading
monomials is linearly independent over its coefficient ring. -/
lemma monic_family_linearIndependent_of_degree_injective
    {D σ ι : Type*} [CommRing D] [Nontrivial D]
    (m : MonomialOrder σ) (p : ι → MvPolynomial σ D)
    (hp : ∀ i, m.Monic (p i))
    (hdeg : Function.Injective (fun i ↦ m.degree (p i))) :
    LinearIndependent D p := by
  classical
  rw [linearIndependent_iff']
  intro s g hrel i hi
  by_contra hgi
  let t := s.filter fun j ↦ g j ≠ 0
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  obtain ⟨k, hkt, hmax⟩ := Finset.exists_max_image t
    (fun j ↦ m.toSyn (m.degree (p j))) ⟨i, hit⟩
  have hks : k ∈ s := (Finset.mem_filter.mp hkt).1
  have hgk : g k ≠ 0 := (Finset.mem_filter.mp hkt).2
  have hcoeff := congrArg
    (fun q : MvPolynomial σ D ↦ q.coeff (m.degree (p k))) hrel
  have hsum : ∑ j ∈ s, g j * (p j).coeff (m.degree (p k)) = g k := by
    calc
      _ = g k * (p k).coeff (m.degree (p k)) := by
        apply Finset.sum_eq_single k
        · intro j hjs hjk
          by_cases hgj : g j = 0
          · simp [hgj]
          · have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, hgj⟩
            have hle := hmax j hjt
            have hdegree_ne : m.degree (p j) ≠ m.degree (p k) := by
              intro heq
              exact hjk (hdeg heq)
            have hsyn_ne : m.toSyn (m.degree (p j)) ≠
                m.toSyn (m.degree (p k)) := by
              intro heq
              exact hdegree_ne (m.toSyn.injective heq)
            have hltSyn : m.toSyn (m.degree (p j)) <
                m.toSyn (m.degree (p k)) := lt_of_le_of_ne hle hsyn_ne
            have hlt : m.degree (p j) ≺[m] m.degree (p k) := hltSyn
            rw [m.coeff_eq_zero_of_lt hlt, mul_zero]
        · intro hknot
          exact (hknot hks).elim
      _ = g k := by rw [(hp k).coeff_degree, mul_one]
  rw [MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_smul, smul_eq_mul,
    MvPolynomial.coeff_zero] at hcoeff
  rw [hsum] at hcoeff
  exact hgk hcoeff

/-- The canonical index type for standard minor products: empty minor
factors are omitted because they represent the unit.  The empty list itself
is retained and indexes the constant polynomial `1`. -/
def StandardMinorProductIndex (n m : ℕ) :=
  {l : List (FinsetMinorIndex n m) //
    IsStandardMinorList l ∧ HasNoEmptyMinors l}

/-- Delete empty-minor factors from a product.  Such factors are equal to
`1`, so this is the canonical representative used by the basis index. -/
def eraseEmptyMinors {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) : List (FinsetMinorIndex n m) :=
  l.filter fun d ↦ d.rows.Nonempty

lemma isStandardMinorList_of_pairwise {n m : ℕ}
    {l : List (FinsetMinorIndex n m)}
    (hl : l.Pairwise (· ≼ᵢ ·)) : IsStandardMinorList l := by
  induction l with
  | nil => trivial
  | cons d l ih =>
      cases l with
      | nil => trivial
      | cons e l =>
          constructor
          · exact (List.pairwise_cons.mp hl).1 e (by simp)
          · exact ih (List.Pairwise.tail hl)

lemma eraseEmptyMinors_standard {n m : ℕ}
    {l : List (FinsetMinorIndex n m)} (hl : IsStandardMinorList l) :
    IsStandardMinorList (eraseEmptyMinors l) := by
  apply isStandardMinorList_of_pairwise
  exact (isStandardMinorList_pairwise hl).filter _

lemma eraseEmptyMinors_hasNoEmptyMinors {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    HasNoEmptyMinors (eraseEmptyMinors l) := by
  intro d hd
  simpa using (List.mem_filter.mp hd).2

lemma FinsetMinorIndex.poly_eq_one_of_not_nonempty
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : ¬d.rows.Nonempty) :
    d.poly = (1 : GenericPoly D n m) := by
  have hrows : d.rows = ∅ := Finset.not_nonempty_iff_eq_empty.mp hd
  have hcols : d.cols = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [← d.card_eq, hrows]
    simp
  unfold FinsetMinorIndex.poly
  rw [hrows, hcols]
  unfold finsetMinorPoly
  rw [dif_pos (by simp)]
  unfold minorPoly
  exact Matrix.det_fin_zero

lemma minorListPoly_eraseEmptyMinors
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) (eraseEmptyMinors l) =
      minorListPoly (D := D) l := by
  induction l with
  | nil => simp [eraseEmptyMinors]
  | cons d l ih =>
      have ih' :
          minorListPoly (D := D)
              (l.filter fun e ↦ e.rows.Nonempty) =
            minorListPoly (D := D) l := by
        simpa only [eraseEmptyMinors] using ih
      by_cases hd : d.rows.Nonempty
      · simp [eraseEmptyMinors, hd, ih']
      · have hdpoly := FinsetMinorIndex.poly_eq_one_of_not_nonempty
          (D := D) d hd
        simp [eraseEmptyMinors, hd, hdpoly, ih']

/-- After the `X ↦ YZ` substitution, standard products indexed without
empty minor factors form a linearly independent family. -/
theorem standardYZHom_standardMinorProducts_linearIndependent
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ} :
    LinearIndependent D
      (fun s : StandardMinorProductIndex n m ↦
        standardYZHom D n m (minorListPoly (D := D) s.1)) := by
  apply monic_family_linearIndependent_of_degree_injective
    (m := (MonomialOrder.lex : MonomialOrder (StandardAuxVar n m)))
  · intro s
    exact (standardYZHom_minorListPoly_degree_code_monic
      (D := D) s.1 s.2.2).2
  · intro s t hdegree
    have hs := standardYZHom_minorListPoly_degree_code_monic
      (D := D) s.1 s.2.2
    have ht := standardYZHom_minorListPoly_degree_code_monic
      (D := D) t.1 t.2.2
    apply Subtype.ext
    apply standardDiagonalCode_injective_on_standard
      s.2.1 t.2.1 s.2.2 t.2.2
    rw [← hs.1, ← ht.1]
    exact hdegree

/-- Standard products of nonempty minors are linearly independent in the
original generic polynomial ring. -/
theorem standardMinorProducts_linearIndependent
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ} :
    LinearIndependent D
      (fun s : StandardMinorProductIndex n m ↦
        minorListPoly (D := D) s.1) := by
  rw [linearIndependent_iff']
  intro s g hrel i hi
  have hmapped :=
    (standardYZHom_standardMinorProducts_linearIndependent
      (D := D) (n := n) (m := m))
  apply (linearIndependent_iff'.mp hmapped) s g ?_ i hi
  apply_fun standardYZHom D n m at hrel
  simpa only [map_sum, map_smul, map_zero] using hrel

/-- The indexed standard products span the full generic polynomial ring. -/
theorem standardMinorProducts_span_eq_top
    (D : Type*) [CommRing D] (n m : ℕ) :
    Submodule.span D
      (Set.range fun s : StandardMinorProductIndex n m ↦
        minorListPoly (D := D) s.1) = ⊤ := by
  apply top_unique
  rw [← standardMinorProductSubmodule_eq_top D n m]
  rw [standardMinorProductSubmodule, Submodule.span_le]
  rintro y ⟨l, hl, rfl⟩
  let s : StandardMinorProductIndex n m :=
    ⟨eraseEmptyMinors l, eraseEmptyMinors_standard hl,
      eraseEmptyMinors_hasNoEmptyMinors l⟩
  rw [← minorListPoly_eraseEmptyMinors (D := D) l]
  exact Submodule.subset_span (Set.mem_range_self s)

/-- The standard products of nonempty minors, including the empty product
`1`, form a basis of the generic polynomial ring. -/
noncomputable def standardMinorProductBasis
    (D : Type*) [CommRing D] [Nontrivial D] (n m : ℕ) :
    Module.Basis (StandardMinorProductIndex n m) D (GenericPoly D n m) :=
  Module.Basis.mk (standardMinorProducts_linearIndependent
      (D := D) (n := n) (m := m)) (by
    rw [standardMinorProducts_span_eq_top D n m])

@[simp] lemma standardMinorProductBasis_apply
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (s : StandardMinorProductIndex n m) :
    standardMinorProductBasis D n m s = minorListPoly (D := D) s.1 := by
  exact Module.Basis.mk_apply _ _ s

end GenericMaximalMinor

end
end
end

section
section
/-!
# The maximal-minor filtration in the standard-product basis

This file refines straightening by recording a prefix of maximal minors.
For a standard product, all maximal factors occur first, so this prefix is
the basis-theoretic filtration by powers of the maximal-minor ideal.
-/

noncomputable section

open scoped BigOperators

namespace GenericMaximalMinor

/-- A finite-set minor of an `n × m` matrix is maximal when its row set has
all `n` possible rows. -/
def FinsetMinorIndex.IsMaximal {n m : ℕ}
    (d : FinsetMinorIndex n m) : Prop := d.rows.card = n

/-- The first `r` factors of a list are maximal.  This recursive formulation
is more convenient for the straightening induction than `List.take`. -/
def HasMaximalPrefix {n m : ℕ} :
    ℕ → List (FinsetMinorIndex n m) → Prop
  | 0, _ => True
  | _ + 1, [] => False
  | r + 1, d :: l => d.IsMaximal ∧ HasMaximalPrefix r l

@[simp] lemma hasMaximalPrefix_zero {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) : HasMaximalPrefix 0 l := by
  trivial

@[simp] lemma hasMaximalPrefix_succ_nil {n m r : ℕ} :
    ¬HasMaximalPrefix (n := n) (m := m) (r + 1) [] := by
  simp [HasMaximalPrefix]

@[simp] lemma hasMaximalPrefix_succ_cons {n m r : ℕ}
    (d : FinsetMinorIndex n m) (l : List (FinsetMinorIndex n m)) :
    HasMaximalPrefix (r + 1) (d :: l) ↔
      d.IsMaximal ∧ HasMaximalPrefix r l := by
  rfl

lemma FinsetMinorIndex.card_rows_le {n m : ℕ}
    (d : FinsetMinorIndex n m) : d.rows.card ≤ n := by
  simpa using Finset.card_le_univ d.rows

lemma FinsetMinorIndex.isMaximal_of_le_of_isMaximal {n m : ℕ}
    {a d : FinsetMinorIndex n m} (had : a ≼ᵢ d)
    (hd : d.IsMaximal) : a.IsMaximal := by
  unfold FinsetMinorIndex.IsMaximal at hd ⊢
  have hle : d.rows.card ≤ a.rows.card := card_ge_of_prefixLE had.1
  have ha := a.card_rows_le
  omega

/-- Pair reductions retaining the total sum of the two minor sizes. -/
def sizedPairReductionGeneratorsFor {D : Type*} [CommRing D]
    {n m : ℕ} (d e : FinsetMinorIndex n m) :
    Set (GenericPoly D n m) :=
  {x | ∃ a b : FinsetMinorIndex n m,
    a ≺ᵢ d ∧ a ≼ᵢ b ∧
    a.rows.card + b.rows.card = d.rows.card + e.rows.card ∧
    x = a.poly * b.poly}

def sizedPairReductionSpan {D : Type*} [CommRing D]
    {n m : ℕ} (d e : FinsetMinorIndex n m) :
    AddSubgroup (GenericPoly D n m) :=
  AddSubgroup.closure (sizedPairReductionGeneratorsFor (D := D) d e)

/-- Two-minor straightening with the size-content equality retained. -/
lemma two_minor_mem_sizedPairReductionSpan
    {D : Type*} [CommRing D] {n m : ℕ}
    (d e : FinsetMinorIndex n m) (hnot : ¬d ≼ᵢ e) :
    d.poly * e.poly ∈ sizedPairReductionSpan (D := D) d e := by
  have h := two_minor_straightening (D := D)
    d.rows e.rows d.cols e.cols d.card_eq e.card_eq hnot
  apply (AddSubgroup.closure_le _).mpr ?_ h
  intro x hx
  rcases hx with ⟨A, C, B, E, hAB, hCE, hAd, hBd,
    hAC, hBE, hstrict, htotal, rfl⟩
  let a : FinsetMinorIndex n m := ⟨A, B, hAB⟩
  let b : FinsetMinorIndex n m := ⟨C, E, hCE⟩
  apply AddSubgroup.subset_closure
  refine ⟨a, b, ?_, ⟨hAC, hBE⟩, htotal, rfl⟩
  refine ⟨⟨hAd, hBd⟩, ?_⟩
  intro hab
  have hrows : A = d.rows := congrArg FinsetMinorIndex.rows hab
  have hcols : B = d.cols := congrArg FinsetMinorIndex.cols hab
  rcases hstrict with hs | hs
  · exact hs.2 hrows
  · exact hs.2 hcols

/-- The coefficient-linear span of standard products whose first `r`
factors are maximal minors. -/
def standardMaximalPrefixSubmodule (D : Type*) [CommRing D]
    (n m r : ℕ) : Submodule D (GenericPoly D n m) :=
  Submodule.span D
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ HasMaximalPrefix r l ∧
        x = minorListPoly (D := D) l}

/-- Fixed-length version used internally by the terminating straightening
induction. -/
def standardMaximalPrefixSubmoduleOfLength
    (D : Type*) [CommRing D] (n m r k : ℕ) :
    Submodule D (GenericPoly D n m) :=
  Submodule.span D
    {x | ∃ l : List (FinsetMinorIndex n m),
      IsStandardMinorList l ∧ HasMaximalPrefix r l ∧
        l.length = k ∧ x = minorListPoly (D := D) l}

lemma standard_minorListPoly_mem_maximalPrefixSubmodule
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m))
    (hl : IsStandardMinorList l) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmodule D n m r := by
  apply Submodule.subset_span
  exact ⟨l, hl, hr, rfl⟩

lemma standard_minorListPoly_mem_maximalPrefixSubmoduleOfLength
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m))
    (hl : IsStandardMinorList l) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmoduleOfLength D n m r l.length := by
  apply Submodule.subset_span
  exact ⟨l, hl, hr, rfl, rfl⟩

lemma mul_left_mem_of_mem_submodule_span
    {D R : Type*} [CommRing D] [CommRing R] [Algebra D R]
    (K : Submodule D R) (s : Set R) (c x : R)
    (hgen : ∀ y ∈ s, c * y ∈ K) (hx : x ∈ Submodule.span D s) :
    c * x ∈ K := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using K.add_mem hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        K.smul_mem a hx

/-- Straightening preserves a prescribed prefix of maximal factors and the
total number of factors. -/
theorem minorListPoly_mem_standardMaximalPrefixSubmoduleOfLength
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m)) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmoduleOfLength D n m r l.length := by
  classical
  generalize hk : l.length = k
  induction k using Nat.strong_induction_on generalizing l r with
  | h k outer =>
      cases r with
      | zero =>
          have hstraight := minorListPoly_mem_standardSpanOfLength
            (D := D) l
          apply (AddSubgroup.closure_le
            (standardMaximalPrefixSubmoduleOfLength D n m 0 k).toAddSubgroup).mpr
              ?_ hstraight
          intro x hx
          rcases hx with ⟨u, huStd, huLen, rfl⟩
          apply Submodule.subset_span
          exact ⟨u, huStd, trivial, huLen.trans hk, rfl⟩
      | succ r =>
          cases l with
          | nil => simp [HasMaximalPrefix] at hr
          | cons d t =>
              have htlen : t.length < k := by
                simp only [List.length_cons] at hk
                omega
              have hdmax : d.IsMaximal :=
                (hasMaximalPrefix_succ_cons d t).mp hr |>.1
              have htprefix : HasMaximalPrefix r t :=
                (hasMaximalPrefix_succ_cons d t).mp hr |>.2
              have prepend : ∀ (a : FinsetMinorIndex n m)
                  (s : List (FinsetMinorIndex n m)),
                  a.IsMaximal → IsStandardMinorList s →
                  HasMaximalPrefix r s → s.length < k →
                  minorListPoly (D := D) (a :: s) ∈
                    standardMaximalPrefixSubmoduleOfLength
                      D n m (r + 1) (s.length + 1) := by
                intro a s hamax hs hsprefix hslen
                generalize hdef : a.defect = q
                induction q using Nat.strong_induction_on generalizing a s with
                | h q inner =>
                    cases s with
                    | nil =>
                        cases r with
                        | zero =>
                            exact standard_minorListPoly_mem_maximalPrefixSubmoduleOfLength
                              (D := D) [a] trivial (by
                                exact (hasMaximalPrefix_succ_cons a []).mpr
                                  ⟨hamax, trivial⟩)
                        | succ r => simp [HasMaximalPrefix] at hsprefix
                    | cons b rest =>
                        by_cases hab : a ≼ᵢ b
                        · apply Submodule.subset_span
                          exact ⟨a :: b :: rest, ⟨hab, hs⟩,
                            (hasMaximalPrefix_succ_cons a (b :: rest)).mpr
                              ⟨hamax, hsprefix⟩, rfl, rfl⟩
                        · have hpair := two_minor_mem_sizedPairReductionSpan
                            (D := D) a b hab
                          have hpairTail :
                              (a.poly * b.poly) *
                                  minorListPoly (D := D) rest ∈
                                standardMaximalPrefixSubmoduleOfLength
                                  D n m (r + 1) ((b :: rest).length + 1) := by
                            apply mul_right_mem_of_mem_closure
                              (standardMaximalPrefixSubmoduleOfLength
                                D n m (r + 1) ((b :: rest).length + 1)).toAddSubgroup
                              (sizedPairReductionGeneratorsFor
                                (D := D) a b)
                              (minorListPoly (D := D) rest)
                              (a.poly * b.poly)
                            · intro y hy
                              rcases hy with
                                ⟨a', b', ha'a, ha'b', hsize, rfl⟩
                              have ha'max : a'.IsMaximal :=
                                a'.isMaximal_of_le_of_isMaximal ha'a.1 hamax
                              have hb'prefix :
                                  HasMaximalPrefix r (b' :: rest) := by
                                cases r with
                                | zero => trivial
                                | succ r =>
                                    have hbdata :=
                                      (hasMaximalPrefix_succ_cons b rest).mp hsprefix
                                    have hb'max : b'.IsMaximal := by
                                      have ha_card : a.rows.card = n := hamax
                                      have hb_card : b.rows.card = n := hbdata.1
                                      have ha'_card : a'.rows.card = n := ha'max
                                      have hb'le := b'.card_rows_le
                                      unfold FinsetMinorIndex.IsMaximal
                                      omega
                                    exact ⟨hb'max, hbdata.2⟩
                              have htail :
                                  minorListPoly (D := D) (b' :: rest) ∈
                                    standardMaximalPrefixSubmoduleOfLength
                                      D n m r (b' :: rest).length := by
                                exact outer (b' :: rest).length (by
                                  simpa using hslen) (r := r)
                                    (b' :: rest) hb'prefix rfl
                              rw [mul_assoc]
                              change a'.poly *
                                  minorListPoly (D := D) (b' :: rest) ∈
                                standardMaximalPrefixSubmoduleOfLength
                                  D n m (r + 1) ((b :: rest).length + 1)
                              apply mul_left_mem_of_mem_submodule_span
                                (standardMaximalPrefixSubmoduleOfLength
                                  D n m (r + 1) ((b :: rest).length + 1))
                                {z | ∃ u : List (FinsetMinorIndex n m),
                                  IsStandardMinorList u ∧
                                  HasMaximalPrefix r u ∧
                                  u.length = (b' :: rest).length ∧
                                  z = minorListPoly (D := D) u}
                                a'.poly
                                (minorListPoly (D := D) (b' :: rest))
                              · intro z hz
                                rcases hz with
                                  ⟨u, huStd, huPrefix, huLen, rfl⟩
                                have hdeflt : a'.defect < q :=
                                  (finsetMinorIndex_defect_lt_of_LT ha'a).trans_eq hdef
                                have hpre := inner a'.defect hdeflt a' u
                                  ha'max huStd huPrefix (by
                                    simpa [huLen] using hslen) rfl
                                simpa [huLen] using hpre
                              · exact htail
                            · simpa [sizedPairReductionSpan] using hpair
                          simpa [minorListPoly, mul_assoc] using hpairTail
              have htail := outer t.length htlen (r := r) t htprefix rfl
              change d.poly * minorListPoly (D := D) t ∈
                standardMaximalPrefixSubmoduleOfLength
                  D n m (r + 1) k
              apply mul_left_mem_of_mem_submodule_span
                (standardMaximalPrefixSubmoduleOfLength
                  D n m (r + 1) k)
                {x | ∃ s : List (FinsetMinorIndex n m),
                  IsStandardMinorList s ∧ HasMaximalPrefix r s ∧
                    s.length = t.length ∧
                    x = minorListPoly (D := D) s}
                d.poly (minorListPoly (D := D) t)
              · intro x hx
                rcases hx with ⟨s, hs, hsp, hslen, rfl⟩
                have hp := prepend d s hdmax hs hsp (by
                  simpa [hslen] using htlen)
                have hlength : s.length + 1 = k := by
                  simpa [hslen] using hk
                simpa [hlength] using hp
              · exact htail

theorem minorListPoly_mem_standardMaximalPrefixSubmodule
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m)) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmodule D n m r := by
  have h := minorListPoly_mem_standardMaximalPrefixSubmoduleOfLength
    (D := D) l hr
  apply (show standardMaximalPrefixSubmoduleOfLength D n m r l.length ≤
      standardMaximalPrefixSubmodule D n m r by
    rw [standardMaximalPrefixSubmoduleOfLength, Submodule.span_le]
    rintro x ⟨u, huStd, huPrefix, -, rfl⟩
    exact standard_minorListPoly_mem_maximalPrefixSubmodule
      u huStd huPrefix) h

lemma hasMaximalPrefix_append_right {n m r : ℕ}
    {l : List (FinsetMinorIndex n m)} (u : List (FinsetMinorIndex n m))
    (hl : HasMaximalPrefix r l) : HasMaximalPrefix r (l ++ u) := by
  induction r generalizing l with
  | zero => trivial
  | succ r ih =>
      cases l with
      | nil => simp [HasMaximalPrefix] at hl
      | cons d l =>
          exact ⟨hl.1, ih hl.2⟩

lemma mul_minorListPoly_mem_standardMaximalPrefixSubmodule
    {D : Type*} [CommRing D] {n m r : ℕ}
    (q : GenericPoly D n m) (l : List (FinsetMinorIndex n m))
    (hl : HasMaximalPrefix r l) :
    q * minorListPoly (D := D) l ∈
      standardMaximalPrefixSubmodule D n m r := by
  have hq : q ∈ standardMinorProductSubmodule D n m :=
    mem_standardMinorProductSubmodule q
  induction hq using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨u, huStd, rfl⟩
      have happend := minorListPoly_mem_standardMaximalPrefixSubmodule
        (D := D) (l ++ u) (hasMaximalPrefix_append_right u hl)
      rw [minorListPoly_append] at happend
      simpa [mul_comm] using happend
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using
      (standardMaximalPrefixSubmodule D n m r).add_mem hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        (standardMaximalPrefixSubmodule D n m r).smul_mem a hx

/-- The standard-prefix span is closed under multiplication by arbitrary
ambient polynomials. -/
lemma standardMaximalPrefixSubmodule_mul_mem
    {D : Type*} [CommRing D] {n m r : ℕ}
    (q : GenericPoly D n m) {x : GenericPoly D n m}
    (hx : x ∈ standardMaximalPrefixSubmodule D n m r) :
    q * x ∈ standardMaximalPrefixSubmodule D n m r := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨l, hlStd, hlPrefix, rfl⟩
      exact mul_minorListPoly_mem_standardMaximalPrefixSubmodule
        q l hlPrefix
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using
      (standardMaximalPrefixSubmodule D n m r).add_mem hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using
        (standardMaximalPrefixSubmodule D n m r).smul_mem a hx

/-- The same carrier, packaged as an ideal of the ambient polynomial ring. -/
def standardMaximalPrefixIdeal
    (D : Type*) [CommRing D] (n m r : ℕ) :
    Ideal (GenericPoly D n m) where
  carrier := standardMaximalPrefixSubmodule D n m r
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' q x hx := standardMaximalPrefixSubmodule_mul_mem q hx

@[simp] lemma mem_standardMaximalPrefixIdeal_iff
    {D : Type*} [CommRing D] {n m r : ℕ}
    {x : GenericPoly D n m} :
    x ∈ standardMaximalPrefixIdeal D n m r ↔
      x ∈ standardMaximalPrefixSubmodule D n m r :=
  Iff.rfl

/-- The maximal-minor ideal using the finite-set minor indexing native to
the straightening development. -/
def finsetMaximalMinorIdealOver
    (D : Type*) [CommRing D] (n m : ℕ) :
    Ideal (GenericPoly D n m) :=
  Ideal.span
    {x | ∃ d : FinsetMinorIndex n m,
      d.IsMaximal ∧ x = d.poly}

lemma FinsetMinorIndex.poly_mem_finsetMaximalMinorIdealOver
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : d.IsMaximal) :
    d.poly ∈ finsetMaximalMinorIdealOver D n m := by
  apply Ideal.subset_span
  exact ⟨d, hd, rfl⟩

lemma minorListPoly_eq_map_prod
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex n m)) :
    minorListPoly (D := D) l = (l.map (·.poly)).prod := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [minorListPoly, ih]

lemma hasMaximalPrefix_length_of_forall_mem {n m : ℕ}
    (l : List (FinsetMinorIndex n m))
    (hl : ∀ d ∈ l, d.IsMaximal) :
    HasMaximalPrefix l.length l := by
  induction l with
  | nil => trivial
  | cons d l ih =>
      exact ⟨hl d (by simp), ih (fun e he ↦ hl e (by simp [he]))⟩

lemma minorListPoly_mem_finsetMaximalMinorIdealOver_pow_of_prefix
    {D : Type*} [CommRing D] {n m r : ℕ}
    (l : List (FinsetMinorIndex n m)) (hr : HasMaximalPrefix r l) :
    minorListPoly (D := D) l ∈
      finsetMaximalMinorIdealOver D n m ^ r := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
      cases l with
      | nil => simp [HasMaximalPrefix] at hr
      | cons d l =>
          rw [minorListPoly_cons, pow_succ']
          exact Ideal.mul_mem_mul
            (d.poly_mem_finsetMaximalMinorIdealOver hr.1)
            (ih l hr.2)

theorem standardMaximalPrefixIdeal_le_pow
    (D : Type*) [CommRing D] (n m r : ℕ) :
    standardMaximalPrefixIdeal D n m r ≤
      finsetMaximalMinorIdealOver D n m ^ r := by
  intro x hx
  change x ∈ standardMaximalPrefixSubmodule D n m r at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨l, hlStd, hlPrefix, rfl⟩
      exact minorListPoly_mem_finsetMaximalMinorIdealOver_pow_of_prefix
        l hlPrefix
  | zero => exact Ideal.zero_mem _
  | add x y _ _ hx hy => exact Ideal.add_mem _ hx hy
  | smul a x _ hx =>
      simpa [Algebra.smul_def] using
        (finsetMaximalMinorIdealOver D n m ^ r).mul_mem_left
          (algebraMap D (GenericPoly D n m) a) hx

theorem finsetMaximalMinorIdealOver_pow_le_standardMaximalPrefixIdeal
    (D : Type*) [CommRing D] (n m r : ℕ) :
    finsetMaximalMinorIdealOver D n m ^ r ≤
      standardMaximalPrefixIdeal D n m r := by
  rw [finsetMaximalMinorIdealOver, Submodule.span_pow]
  rw [Ideal.span_le]
  intro x hx
  obtain ⟨f, hf, hprod⟩ := Set.mem_pow_iff_prod.mp hx
  have hex : ∀ i, ∃ d : FinsetMinorIndex n m,
      d.IsMaximal ∧ f i = d.poly := hf
  choose d hdmax hfd using hex
  let l : List (FinsetMinorIndex n m) := List.ofFn d
  have hall : ∀ e ∈ l, e.IsMaximal := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact hdmax i
  have hlprefix : HasMaximalPrefix r l := by
    have h := hasMaximalPrefix_length_of_forall_mem l hall
    simpa [l] using h
  have hlmem := minorListPoly_mem_standardMaximalPrefixSubmodule
    (D := D) l hlprefix
  change minorListPoly (D := D) l ∈
    standardMaximalPrefixIdeal D n m r at hlmem
  have hpoly : minorListPoly (D := D) l = ∏ i, f i := by
    rw [minorListPoly_eq_map_prod]
    simp only [l, List.map_ofFn, List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro i _
    exact (hfd i).symm
  rw [← hprod, ← hpoly]
  exact hlmem

/-- Basis description of every power of the generic maximal-minor ideal. -/
theorem standardMaximalPrefixIdeal_eq_pow
    (D : Type*) [CommRing D] (n m r : ℕ) :
    standardMaximalPrefixIdeal D n m r =
      finsetMaximalMinorIdealOver D n m ^ r := by
  apply le_antisymm
  · exact standardMaximalPrefixIdeal_le_pow D n m r
  · exact finsetMaximalMinorIdealOver_pow_le_standardMaximalPrefixIdeal
      D n m r

/-! ## Bridge to the project's order-embedding maximal-minor ideal -/

/-- The finite-set index corresponding to an increasing choice of `n`
columns. -/
def finsetMaximalIndex {n m : ℕ} (S : MaximalMinorIndex n m) :
    FinsetMinorIndex n m where
  rows := Finset.univ
  cols := Finset.univ.map S.toEmbedding
  card_eq := by simp

@[simp] lemma finsetMaximalIndex_isMaximal {n m : ℕ}
    (S : MaximalMinorIndex n m) : (finsetMaximalIndex S).IsMaximal := by
  simp [finsetMaximalIndex, FinsetMinorIndex.IsMaximal]

lemma orderEmbOfFin_univ_eq_id (n : ℕ)
    (h : (Finset.univ : Finset (Fin n)).card = n) :
    Finset.orderEmbOfFin Finset.univ h = OrderEmbedding.id (Fin n) := by
  symm
  exact Finset.orderEmbOfFin_unique' h (fun i ↦ Finset.mem_univ i)

lemma orderEmbOfFin_map_orderEmbedding_eq {n m : ℕ}
    (S : Fin n ↪o Fin m)
    (h : (Finset.univ.map S.toEmbedding).card = n) :
    (Finset.univ.map S.toEmbedding).orderEmbOfFin h = S := by
  symm
  apply Finset.orderEmbOfFin_unique' h
  intro i
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

lemma finsetMaximalIndex_poly
    {D : Type*} [CommRing D] {n m : ℕ} (hnm : n ≤ m)
    (S : MaximalMinorIndex n m) :
    (finsetMaximalIndex S).poly =
      maximalMinorPolyOver (D := D) hnm S := by
  unfold FinsetMinorIndex.poly
  change finsetMinorPoly (D := D) Finset.univ
      (Finset.univ.map S.toEmbedding) = _
  rw [finsetMinorPoly_of_card_eq (D := D)
    (Finset.univ : Finset (Fin n))
    (Finset.univ.map S.toEmbedding) (by simp)]
  unfold maximalMinorPolyOver
  let A : Finset (Fin n) := Finset.univ
  let B : Finset (Fin m) := Finset.univ.map S.toEmbedding
  have hA : A.card = n := by simp [A]
  have hB : B.card = n := by simp [B]
  have hAB : A.card = B.card := hA.trans hB.symm
  let d₀ : MinorIndex n m := minorIndexOfFinsets A B hAB
  let M : Matrix (Fin A.card) (Fin A.card) (GenericPoly D n m) :=
    minorMatrix d₀
  let N : Matrix (Fin n) (Fin n) (GenericPoly D n m) :=
    minorMatrix (maximalIndex hnm S)
  change Matrix.det M = Matrix.det N
  let e : Fin A.card ≃ Fin n := (Fin.castOrderIso hA).toEquiv
  calc
    Matrix.det M = Matrix.det (M.reindex e e) :=
      (Matrix.det_reindex_self e M).symm
    _ = Matrix.det N := by
      congr 1
      funext i j
      change M (e.symm i) (e.symm j) = N i j
      unfold M N d₀ minorMatrix minorIndexOfFinsets maximalIndex
      congr 2
      · have hcross : A.orderEmbOfFin rfl (e.symm i) =
            A.orderEmbOfFin hA i := by
          apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
          simp [e]
        rw [hcross]
        have hid : A.orderEmbOfFin hA = OrderEmbedding.id (Fin n) := by
          simpa [A] using orderEmbOfFin_univ_eq_id n hA
        rw [hid]
      · have hcross : B.orderEmbOfFin hAB.symm (e.symm j) =
            B.orderEmbOfFin hB j := by
          apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
          simp [e]
        rw [hcross]
        have hS : B.orderEmbOfFin hB = S := by
          simpa [B] using orderEmbOfFin_map_orderEmbedding_eq S hB
        rw [hS]

/-- Recover the increasing column embedding from a maximal finite-set
minor index. -/
def FinsetMinorIndex.maximalOrderEmbedding {n m : ℕ}
    (d : FinsetMinorIndex n m) (hd : d.IsMaximal) :
    MaximalMinorIndex n m :=
  d.cols.orderEmbOfFin (by
    rw [← d.card_eq]
    exact hd)

lemma FinsetMinorIndex.eq_finsetMaximalIndex_maximalOrderEmbedding
    {n m : ℕ} (d : FinsetMinorIndex n m) (hd : d.IsMaximal) :
    d = finsetMaximalIndex (d.maximalOrderEmbedding hd) := by
  apply finsetMinorIndex_ext
  · apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa using (Nat.le_of_eq hd.symm)
  · change d.cols = Finset.univ.map
        (d.cols.orderEmbOfFin (by rw [← d.card_eq]; exact hd)).toEmbedding
    symm
    exact Finset.map_orderEmbOfFin_univ d.cols
      (by rw [← d.card_eq]; exact hd)

/-- The finite-set and order-embedding presentations generate the same
maximal-minor ideal. -/
theorem finsetMaximalMinorIdealOver_eq_maximalMinorIdealOver
    (D : Type*) [CommRing D] {n m : ℕ} (hnm : n ≤ m) :
    finsetMaximalMinorIdealOver D n m =
      maximalMinorIdealOver D n m hnm := by
  apply le_antisymm
  · rw [finsetMaximalMinorIdealOver, Ideal.span_le]
    rintro x ⟨d, hd, rfl⟩
    rw [d.eq_finsetMaximalIndex_maximalOrderEmbedding hd,
      finsetMaximalIndex_poly (D := D) hnm]
    exact maximalMinorPolyOver_mem_ideal hnm _
  · rw [maximalMinorIdealOver, Ideal.span_le]
    rintro x ⟨S, rfl⟩
    rw [← finsetMaximalIndex_poly (D := D) hnm S]
    exact (finsetMaximalIndex S).poly_mem_finsetMaximalMinorIdealOver
      (finsetMaximalIndex_isMaximal S)

/-- Paper-facing basis description of every power of the existing generic
maximal-minor ideal. -/
theorem standardMaximalPrefixIdeal_eq_maximalMinorIdealOver_pow
    (D : Type*) [CommRing D] {n m : ℕ} (hnm : n ≤ m) (r : ℕ) :
    standardMaximalPrefixIdeal D n m r =
      maximalMinorIdealOver D n m hnm ^ r := by
  rw [standardMaximalPrefixIdeal_eq_pow,
    finsetMaximalMinorIdealOver_eq_maximalMinorIdealOver D hnm]

/-! ## The corner factor -/

/-- The bottom-right `1 × 1` minor. -/
def cornerMinorIndex (n m : ℕ) : FinsetMinorIndex (n + 1) (m + 1) :=
  singletonMinorIndex (Fin.last n) (Fin.last m)

@[simp] lemma cornerMinorIndex_poly
    {D : Type*} [CommRing D] (n m : ℕ) :
    (cornerMinorIndex n m).poly =
      (MvPolynomial.X (Fin.last n, Fin.last m) :
        GenericPoly D (n + 1) (m + 1)) := by
  exact singletonMinorIndex_poly (Fin.last n) (Fin.last m)

@[simp] lemma cornerMinorIndex_rows_nonempty (n m : ℕ) :
    (cornerMinorIndex n m).rows.Nonempty := by
  simp [cornerMinorIndex, singletonMinorIndex]

lemma hasMaximalPrefix_eraseEmptyMinors
    {n m r : ℕ} (hn : 0 < n)
    {l : List (FinsetMinorIndex n m)} (hl : HasMaximalPrefix r l) :
    HasMaximalPrefix r (eraseEmptyMinors l) := by
  induction r generalizing l with
  | zero => trivial
  | succ r ih =>
      cases l with
      | nil => simp [HasMaximalPrefix] at hl
      | cons d l =>
          have hdmax : d.IsMaximal := hl.1
          have hdne : d.rows.Nonempty := by
            apply Finset.card_pos.mp
            rw [hdmax]
            exact hn
          change HasMaximalPrefix (r + 1)
            ((d :: l).filter fun e ↦ e.rows.Nonempty)
          simp only [List.filter_cons, decide_eq_true_eq, if_pos hdne,
            hasMaximalPrefix_succ_cons]
          exact ⟨hdmax, ih hl.2⟩

/-- The span of the subset of the standard basis having a maximal prefix. -/
def standardBasisPrefixSubmodule
    (D : Type*) [CommRing D] [Nontrivial D] (n m r : ℕ) :
    Submodule D (GenericPoly D n m) :=
  let b := standardMinorProductBasis D n m
  Submodule.span D
    (b '' {s : StandardMinorProductIndex n m |
      HasMaximalPrefix r s.1})

theorem standardMaximalPrefixSubmodule_eq_standardBasisPrefixSubmodule
    (D : Type*) [CommRing D] [Nontrivial D]
    {n m : ℕ} (hn : 0 < n) (r : ℕ) :
    standardMaximalPrefixSubmodule D n m r =
      standardBasisPrefixSubmodule D n m r := by
  apply le_antisymm
  · rw [standardMaximalPrefixSubmodule, Submodule.span_le]
    rintro x ⟨l, hlStd, hlPrefix, rfl⟩
    let s : StandardMinorProductIndex n m :=
      ⟨eraseEmptyMinors l, eraseEmptyMinors_standard hlStd,
        eraseEmptyMinors_hasNoEmptyMinors l⟩
    have hsPrefix : HasMaximalPrefix r s.1 :=
      hasMaximalPrefix_eraseEmptyMinors hn hlPrefix
    rw [← minorListPoly_eraseEmptyMinors (D := D) l]
    change minorListPoly (D := D) s.1 ∈
      standardBasisPrefixSubmodule D n m r
    rw [← standardMinorProductBasis_apply (D := D) s]
    apply Submodule.subset_span
    exact ⟨s, hsPrefix, rfl⟩
  · rw [standardBasisPrefixSubmodule, Submodule.span_le]
    rintro x ⟨s, hsPrefix, rfl⟩
    rw [standardMinorProductBasis_apply]
    exact standard_minorListPoly_mem_maximalPrefixSubmodule
      s.1 s.2.1 hsPrefix

end GenericMaximalMinor

end
end
end

section
section
/-!
# A weight valuation for generic maximal minors

This file tags selected auxiliary variables by a new univariate variable.
The trailing degree of the resulting polynomial records the least selected
weight occurring in the original multivariate polynomial.  It will be
applied to the last inner `Y`-column in the standard `X ↦ YZ` substitution.
-/

noncomputable section

open scoped BigOperators MonomialOrder

namespace GenericMaximalMinor

section WeightTag

variable {D σ : Type*} [CommSemiring D]

/-- The additive weight of a multivariate monomial exponent. -/
def monomialWeight (w : σ → ℕ) (d : σ →₀ ℕ) : ℕ :=
  d.sum fun i e ↦ e * w i

@[simp] lemma monomialWeight_zero (w : σ → ℕ) :
    monomialWeight w 0 = 0 := by
  simp [monomialWeight]

/-- Retain every old variable in the coefficient ring and additionally tag
it by `X ^ w i`.  Retaining the old variable makes the transformation
injective on monomials. -/
def weightTagHom (w : σ → ℕ) :
    MvPolynomial σ D →+* Polynomial (MvPolynomial σ D) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : MvPolynomial σ D →+*
      Polynomial (MvPolynomial σ D)).comp MvPolynomial.C)
    (fun i ↦ Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)

@[simp] lemma weightTagHom_C (w : σ → ℕ) (a : D) :
    weightTagHom w (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
  simp [weightTagHom]

@[simp] lemma weightTagHom_X (w : σ → ℕ) (i : σ) :
    weightTagHom w (MvPolynomial.X i) =
      Polynomial.C (MvPolynomial.X i : MvPolynomial σ D) *
        Polynomial.X ^ w i := by
  simp [weightTagHom]

/-- A tagged monomial remains a single monomial; its new exponent is its
additive weight and its coefficient remembers the entire old monomial. -/
lemma weightTagHom_monomial (w : σ → ℕ) (d : σ →₀ ℕ) (a : D) :
    weightTagHom w (MvPolynomial.monomial d a) =
      Polynomial.monomial (monomialWeight w d)
        (MvPolynomial.monomial d a) := by
  classical
  rw [weightTagHom, MvPolynomial.eval₂Hom_monomial]
  simp only [RingHom.coe_comp, Function.comp_apply]
  change Polynomial.C (MvPolynomial.C a) *
      (∏ i ∈ d.support,
        (Polynomial.C (MvPolynomial.X i) *
          Polynomial.X ^ w i) ^ d i) = _
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  have hCpow (i : σ) :
      (Polynomial.C (MvPolynomial.X i : MvPolynomial σ D)) ^ d i =
        Polynomial.C ((MvPolynomial.X i : MvPolynomial σ D) ^ d i) := by
    exact (map_pow Polynomial.C
      (MvPolynomial.X i : MvPolynomial σ D) (d i)).symm
  simp_rw [hCpow]
  have hCprod :
      (∏ i ∈ d.support,
        Polynomial.C ((MvPolynomial.X i : MvPolynomial σ D) ^ d i)) =
        Polynomial.C (∏ i ∈ d.support,
          (MvPolynomial.X i : MvPolynomial σ D) ^ d i) := by
    exact (map_prod Polynomial.C
      (fun i ↦ (MvPolynomial.X i : MvPolynomial σ D) ^ d i)
      d.support).symm
  rw [hCprod]
  rw [MvPolynomial.prod_X_pow_eq_monomial]
  rw [← mul_assoc, ← map_mul]
  rw [MvPolynomial.C_mul_monomial]
  simp only [mul_one]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp [monomialWeight, Finsupp.sum, mul_comm]

lemma weightTagHom_eq_sum (w : σ → ℕ) (p : MvPolynomial σ D) :
    weightTagHom w p =
      ∑ d ∈ p.support,
        Polynomial.monomial (monomialWeight w d)
          (MvPolynomial.monomial d (p.coeff d)) := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum, weightTagHom_monomial]

/-- Exact recovery formula for every old and new exponent. -/
lemma coeff_coeff_weightTagHom_eq_ite (w : σ → ℕ)
    (p : MvPolynomial σ D) (d : σ →₀ ℕ) (k : ℕ) :
    MvPolynomial.coeff d ((weightTagHom w p).coeff k) =
      if monomialWeight w d = k then p.coeff d else 0 := by
  classical
  rw [weightTagHom_eq_sum]
  change (MvPolynomial.lcoeff D d)
      ((Polynomial.lcoeff (MvPolynomial σ D) k)
        (∑ e ∈ p.support,
          Polynomial.monomial (monomialWeight w e)
            (MvPolynomial.monomial e (p.coeff e)))) = _
  simp only [map_sum, Polynomial.lcoeff_apply,
    MvPolynomial.lcoeff_apply, Polynomial.coeff_monomial]
  by_cases hd : d ∈ p.support
  · rw [Finset.sum_eq_single d]
    · by_cases hw : monomialWeight w d = k
      · rw [if_pos hw, MvPolynomial.coeff_monomial,
          if_pos rfl, if_pos hw]
      · rw [if_neg hw, MvPolynomial.coeff_zero, if_neg hw]
    · intro e he hed
      by_cases hw : monomialWeight w e = k
      · rw [if_pos hw, MvPolynomial.coeff_monomial]
        exact if_neg hed
      · rw [if_neg hw, MvPolynomial.coeff_zero]
    · intro hnot
      exact (hnot hd).elim
  · have hcoeff : p.coeff d = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hd
    rw [hcoeff]
    simp only [ite_self]
    apply Finset.sum_eq_zero
    intro e he
    have hed : e ≠ d := by
      intro hed
      subst e
      exact hd he
    by_cases hw : monomialWeight w e = k
    · rw [if_pos hw, MvPolynomial.coeff_monomial]
      exact if_neg hed
    · rw [if_neg hw, MvPolynomial.coeff_zero]

/-- The coefficient of the tagged polynomial at the weight of `d` still
has old monomial coefficient `p.coeff d` at the old exponent `d`. -/
lemma coeff_coeff_weightTagHom (w : σ → ℕ)
    (p : MvPolynomial σ D) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d
        ((weightTagHom w p).coeff (monomialWeight w d)) =
      p.coeff d := by
  simpa using coeff_coeff_weightTagHom_eq_ite w p d (monomialWeight w d)

lemma support_coeff_weightTagHom_subset (w : σ → ℕ)
    (p : MvPolynomial σ D) (k : ℕ) :
    ((weightTagHom w p).coeff k).support ⊆ p.support := by
  intro d hd
  have hcoeff : MvPolynomial.coeff d
      ((weightTagHom w p).coeff k) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [coeff_coeff_weightTagHom_eq_ite] at hcoeff
  by_cases hw : monomialWeight w d = k
  · rw [if_pos hw] at hcoeff
    exact MvPolynomial.mem_support_iff.mpr hcoeff
  · rw [if_neg hw] at hcoeff
    exact (hcoeff rfl).elim

/-- The weight tag is injective: the coefficient ring remembers every old
monomial, while the new polynomial exponent records only its weight. -/
lemma weightTagHom_injective (w : σ → ℕ) :
    Function.Injective (weightTagHom (D := D) w) := by
  intro p q hpq
  apply MvPolynomial.ext
  intro d
  rw [← coeff_coeff_weightTagHom w p d,
    ← coeff_coeff_weightTagHom w q d, hpq]

end WeightTag

section ZeroWeight

variable {D σ : Type*} [CommSemiring D]

/-- Set all positive-weight variables to zero and retain the weight-zero
variables. -/
def zeroWeightHom (w : σ → ℕ) :
    MvPolynomial σ D →+* MvPolynomial σ D :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ if w i = 0 then MvPolynomial.X i else 0)

@[simp] lemma zeroWeightHom_C (w : σ → ℕ) (a : D) :
    zeroWeightHom w (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [zeroWeightHom]

@[simp] lemma zeroWeightHom_X (w : σ → ℕ) (i : σ) :
    zeroWeightHom w (MvPolynomial.X i : MvPolynomial σ D) =
      if w i = 0 then (MvPolynomial.X i : MvPolynomial σ D) else 0 := by
  simp [zeroWeightHom]

/-- The constant coefficient of the tag is obtained by setting every
positive-weight old variable to zero. -/
lemma coeff_zero_weightTagHom (w : σ → ℕ) (p : MvPolynomial σ D) :
    (weightTagHom w p).coeff 0 = zeroWeightHom w p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hhom :
      (Polynomial.evalRingHom (0 : MvPolynomial σ D)).comp
          (weightTagHom (D := D) w) =
        zeroWeightHom w := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [weightTagHom, zeroWeightHom]
    · intro i
      by_cases hi : w i = 0
      · simp [weightTagHom, zeroWeightHom, hi]
      · simp [weightTagHom, zeroWeightHom, hi]
  exact RingHom.congr_fun hhom p

end ZeroWeight

section LastYWeight

/-- Weight one precisely on the auxiliary `Y` variables in the final inner
column, and weight zero on every other auxiliary variable. -/
def lastYVarWeight (n m : ℕ) : StandardAuxVar (n + 1) m → ℕ :=
  fun v ↦
    if (ofLex v).1 = Fin.last n then
      match ofLex (ofLex v).2 with
      | Sum.inl _ => 1
      | Sum.inr _ => 0
    else 0

@[simp] lemma lastYVarWeight_standardAuxYVar_last
    {n m : ℕ} (i : Fin (n + 1)) :
    lastYVarWeight n m (standardAuxYVar (Fin.last n) i) = 1 := by
  simp [lastYVarWeight, standardAuxYVar]

@[simp] lemma lastYVarWeight_standardAuxYVar_of_ne
    {n m : ℕ} (q i : Fin (n + 1)) (hq : q ≠ Fin.last n) :
    lastYVarWeight n m (standardAuxYVar q i) = 0 := by
  simp [lastYVarWeight, standardAuxYVar, hq]

@[simp] lemma lastYVarWeight_standardAuxZVar
    {n m : ℕ} (q : Fin (n + 1)) (j : Fin m) :
    lastYVarWeight n m (standardAuxZVar q j) = 0 := by
  by_cases hq : q = Fin.last n
  · subst q
    simp [lastYVarWeight, standardAuxZVar]
  · simp [lastYVarWeight, standardAuxZVar, hq]

/-- The abstract monomial weight is the sum of the exponents of the final
inner-column `Y` variables. -/
lemma monomialWeight_lastYVarWeight {n m : ℕ}
    (d : StandardAuxVar (n + 1) m →₀ ℕ) :
    monomialWeight (lastYVarWeight n m) d =
      ∑ i : Fin (n + 1), d (standardAuxYVar (Fin.last n) i) := by
  classical
  rw [monomialWeight, Finsupp.sum_fintype]
  · let e : (Fin (n + 1) × (Fin (n + 1) ⊕ Fin m)) ≃
        StandardAuxVar (n + 1) m :=
      (Equiv.prodCongr (Equiv.refl _) toLex).trans toLex
    rw [← e.sum_comp]
    rw [Fintype.sum_prod_type]
    simp [e, Fintype.sum_sum_type, lastYVarWeight,
      standardAuxYVar]
  · intro i
    simp

/-- Number of maximal-minor factors in a product.  On a standard product
these are exactly its initial maximal factors. -/
def maximalMinorCount {n m : ℕ} :
    List (FinsetMinorIndex n m) → ℕ
  | [] => 0
  | d :: l => if d.rows.card = n then maximalMinorCount l + 1
      else maximalMinorCount l

@[simp] lemma maximalMinorCount_nil {n m : ℕ} :
    maximalMinorCount ([] : List (FinsetMinorIndex n m)) = 0 := rfl

@[simp] lemma maximalMinorCount_cons {n m : ℕ}
    (d : FinsetMinorIndex n m) (l : List (FinsetMinorIndex n m)) :
    maximalMinorCount (d :: l) =
      if d.rows.card = n then maximalMinorCount l + 1
      else maximalMinorCount l := rfl

lemma isStandardMinorList_tail {n m : ℕ}
    (d : FinsetMinorIndex n m) (l : List (FinsetMinorIndex n m))
    (hl : IsStandardMinorList (d :: l)) : IsStandardMinorList l := by
  cases l with
  | nil => trivial
  | cons e l => exact hl.2

lemma maximalMinorCount_eq_zero_of_standard_head_not_maximal
    {n m : ℕ} (d : FinsetMinorIndex n m)
    (l : List (FinsetMinorIndex n m))
    (hl : IsStandardMinorList (d :: l)) (hd : ¬d.IsMaximal) :
    maximalMinorCount (d :: l) = 0 := by
  induction l generalizing d with
  | nil =>
      unfold FinsetMinorIndex.IsMaximal at hd
      simp [maximalMinorCount, hd]
  | cons e l ih =>
      have hde : d ≼ᵢ e := hl.1
      have he : ¬e.IsMaximal := by
        intro he
        exact hd (d.isMaximal_of_le_of_isMaximal hde he)
      have htail : IsStandardMinorList (e :: l) := hl.2
      have hdcard : ¬d.rows.card = n := by
        simpa [FinsetMinorIndex.IsMaximal] using hd
      rw [maximalMinorCount_cons, if_neg hdcard]
      exact ih e htail he

/-- On a standard list the maximal factors form exactly an initial segment,
so a prefix of length `r` exists precisely when the total maximal count is
at least `r`. -/
lemma hasMaximalPrefix_iff_le_maximalMinorCount {n m r : ℕ}
    (l : List (FinsetMinorIndex n m)) (hl : IsStandardMinorList l) :
    HasMaximalPrefix r l ↔ r ≤ maximalMinorCount l := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
      cases l with
      | nil => simp [HasMaximalPrefix]
      | cons d l =>
          by_cases hd : d.IsMaximal
          · have htail := isStandardMinorList_tail d l hl
            have hdcard : d.rows.card = n := hd
            simp [HasMaximalPrefix, maximalMinorCount, hd, hdcard,
              ih l htail]
          · have hzero :=
              maximalMinorCount_eq_zero_of_standard_head_not_maximal d l hl hd
            simp [HasMaximalPrefix, hd, hzero]

/-- Reading the final possible row position keeps precisely the maximal
minor factors. -/
lemma minorRowProfile_last_card {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m)) :
    (minorRowProfile l n).card = maximalMinorCount l := by
  change (minorRowColumn l n).length = maximalMinorCount l
  induction l with
  | nil => simp [minorRowColumn]
  | cons d l ih =>
      by_cases hd : d.IsMaximal
      · have hlt : n < d.rows.card := by
          unfold FinsetMinorIndex.IsMaximal at hd
          omega
        change (List.filterMap (fun x ↦ x.rowAt? n) (d :: l)).length = _
        rw [List.filterMap_cons,
          FinsetMinorIndex.rowAt?_eq_some d n hlt]
        change (minorRowColumn l n).length + 1 = _
        rw [ih]
        unfold FinsetMinorIndex.IsMaximal at hd
        simp [maximalMinorCount, hd]
      · have hle : d.rows.card ≤ n := by
          have hcard := d.card_rows_le
          unfold FinsetMinorIndex.IsMaximal at hd
          omega
        change (List.filterMap (fun x ↦ x.rowAt? n) (d :: l)).length = _
        rw [List.filterMap_cons,
          FinsetMinorIndex.rowAt?_eq_none d n hle]
        change (minorRowColumn l n).length = _
        rw [ih]
        unfold FinsetMinorIndex.IsMaximal at hd
        simp [maximalMinorCount, hd]

/-- The diagonal leading exponent of a standard product has final-`Y`
weight equal to the number of maximal-minor factors. -/
lemma monomialWeight_standardDiagonalCode {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m)) :
    monomialWeight (lastYVarWeight n m) (standardDiagonalCode l) =
      maximalMinorCount l := by
  rw [monomialWeight_lastYVarWeight]
  simp only [standardDiagonalCode_row_apply, Fin.val_last]
  calc
    ∑ i : Fin (n + 1), Multiset.count i (minorRowProfile l n) =
        (minorRowProfile l n).card := by
      simpa using Multiset.sum_count_eq_card
        (s := (Finset.univ : Finset (Fin (n + 1))))
        (m := minorRowProfile l n) (by simp)
    _ = maximalMinorCount l := minorRowProfile_last_card l

/-- After `X ↦ YZ`, a maximal minor has zero weight-zero component: an
injective choice of all `n+1` inner indices must use the final one. -/
lemma coeff_zero_weightTag_standardYZHom_maximalMinor
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex (n + 1) m) (hd : d.IsMaximal) :
    (weightTagHom (lastYVarWeight n m)
        (standardYZHom D (n + 1) m d.poly)).coeff 0 = 0 := by
  rw [coeff_zero_weightTagHom]
  rw [standardYZHom_finsetMinorIndex_poly_injective_expansion]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro f hf
  have hinj : Function.Injective f :=
    (Finset.mem_filter.mp hf).2
  have hcard : Fintype.card (Fin d.rows.card) =
      Fintype.card (Fin (n + 1)) := by
    simpa [FinsetMinorIndex.IsMaximal] using hd
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  obtain ⟨i, hi⟩ := hbij.2 (Fin.last n)
  have hyzero :
      zeroWeightHom (D := D) (lastYVarWeight n m)
          (∏ j, auxY (D := D) (d.rows.orderEmbOfFin rfl j) (f j)) = 0 := by
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hi]
    simp [auxY, zeroWeightHom]
  rw [map_mul, hyzero, zero_mul]

/-- The composite `X ↦ YZ` substitution followed by the final-`Y` weight
tag. -/
def maximalMinorWeightHom (D : Type*) [CommSemiring D] (n m : ℕ) :
    GenericPoly D (n + 1) m →+*
      Polynomial (StandardAuxPoly D (n + 1) m) :=
  (weightTagHom (D := D) (lastYVarWeight n m)).comp
    (standardYZHom D (n + 1) m).toRingHom

lemma X_dvd_maximalMinorWeightHom_minor_of_maximal
    {D : Type*} [CommRing D] {n m : ℕ}
    (d : FinsetMinorIndex (n + 1) m) (hd : d.IsMaximal) :
    Polynomial.X ∣ maximalMinorWeightHom D n m d.poly := by
  rw [Polynomial.X_dvd_iff]
  exact coeff_zero_weightTag_standardYZHom_maximalMinor d hd

/-- Every maximal factor supplies one factor of the tag variable. -/
lemma X_pow_maximalMinorCount_dvd_maximalMinorWeightHom_minorListPoly
    {D : Type*} [CommRing D] {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m)) :
    Polynomial.X ^ maximalMinorCount l ∣
      maximalMinorWeightHom D n m (minorListPoly (D := D) l) := by
  induction l with
  | nil => simp [maximalMinorWeightHom, minorListPoly]
  | cons d l ih =>
      rw [minorListPoly_cons, map_mul]
      by_cases hd : d.IsMaximal
      · have hx := X_dvd_maximalMinorWeightHom_minor_of_maximal
          (D := D) d hd
        have hmul := mul_dvd_mul hx ih
        unfold FinsetMinorIndex.IsMaximal at hd
        simpa [maximalMinorCount, hd, pow_succ', mul_comm,
          mul_left_comm, mul_assoc] using hmul
      · have hright := dvd_mul_of_dvd_right ih
          (maximalMinorWeightHom D n m d.poly)
        unfold FinsetMinorIndex.IsMaximal at hd
        simpa [maximalMinorCount, hd] using hright

/-- The first nonzero tagged coefficient retains the same monic diagonal
leading term as the original standard product. -/
lemma trailingCoeffSlice_degree_code_monic
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (l : List (FinsetMinorIndex (n + 1) m))
    (hne : HasNoEmptyMinors l) :
    let S := (maximalMinorWeightHom D n m
      (minorListPoly (D := D) l)).coeff (maximalMinorCount l)
    (MonomialOrder.lex : MonomialOrder (StandardAuxVar (n + 1) m)).degree S =
        standardDiagonalCode l ∧
      (MonomialOrder.lex : MonomialOrder (StandardAuxVar (n + 1) m)).Monic S := by
  let P : StandardAuxPoly D (n + 1) m :=
    standardYZHom D (n + 1) m (minorListPoly (D := D) l)
  let S : StandardAuxPoly D (n + 1) m :=
    (maximalMinorWeightHom D n m
      (minorListPoly (D := D) l)).coeff (maximalMinorCount l)
  let ord : MonomialOrder (StandardAuxVar (n + 1) m) := MonomialOrder.lex
  have hlead := standardYZHom_minorListPoly_degree_code_monic
    (D := D) l hne
  have hcodecoeff : S.coeff (standardDiagonalCode l) = 1 := by
    change MvPolynomial.coeff (standardDiagonalCode l)
      ((weightTagHom (D := D) (lastYVarWeight n m) P).coeff
        (maximalMinorCount l)) = 1
    rw [← monomialWeight_standardDiagonalCode l,
      coeff_coeff_weightTagHom]
    change (standardYZHom D (n + 1) m
      (minorListPoly (D := D) l)).coeff (standardDiagonalCode l) = 1
    rw [← hlead.1]
    exact hlead.2.coeff_degree
  have hcodeMem : standardDiagonalCode l ∈ S.support :=
    MvPolynomial.mem_support_iff.mpr (by
      rw [hcodecoeff]
      exact one_ne_zero)
  have hupper : ord.toSyn (ord.degree S) ≤
      ord.toSyn (standardDiagonalCode l) := by
    rw [ord.degree_le_iff]
    intro d hd
    have hdP : d ∈ P.support := by
      apply support_coeff_weightTagHom_subset
        (w := lastYVarWeight n m) (p := P)
      exact hd
    have hle := ord.le_degree hdP
    change ord.toSyn d ≤ ord.toSyn (ord.degree P) at hle
    simpa [P, ord, hlead.1] using hle
  have hlower : ord.toSyn (standardDiagonalCode l) ≤
      ord.toSyn (ord.degree S) := ord.le_degree hcodeMem
  have hdegree : ord.degree S = standardDiagonalCode l := by
    apply ord.toSyn.injective
    exact le_antisymm hupper hlower
  constructor
  · exact hdegree
  · rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff, hdegree]
    exact hcodecoeff

/-- The first tagged coefficient of every standard basis product is a
linearly independent family. -/
lemma trailingCoeffSlice_standardBasis_linearIndependent
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ} :
    LinearIndependent D
      (fun s : StandardMinorProductIndex (n + 1) m ↦
        (maximalMinorWeightHom D n m
          (minorListPoly (D := D) s.1)).coeff
            (maximalMinorCount s.1)) := by
  apply monic_family_linearIndependent_of_degree_injective
    (m := (MonomialOrder.lex :
      MonomialOrder (StandardAuxVar (n + 1) m)))
  · intro s
    exact (trailingCoeffSlice_degree_code_monic
      (D := D) s.1 s.2.2).2
  · intro s t hdegree
    have hs := (trailingCoeffSlice_degree_code_monic
      (D := D) s.1 s.2.2).1
    have ht := (trailingCoeffSlice_degree_code_monic
      (D := D) t.1 t.2.2).1
    apply Subtype.ext
    apply standardDiagonalCode_injective_on_standard
      s.2.1 t.2.1 s.2.2 t.2.2
    rw [← hs, ← ht]
    exact hdegree

lemma maximalMinorWeightHom_coeff_smul
    {D : Type*} [CommRing D] {n m k : ℕ}
    (a : D) (f : GenericPoly D (n + 1) m) :
    (maximalMinorWeightHom D n m (a • f)).coeff k =
      a • (maximalMinorWeightHom D n m f).coeff k := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul]
  rw [show maximalMinorWeightHom D n m (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) by
    simp [maximalMinorWeightHom, standardYZHom, weightTagHom]]
  rw [Polynomial.coeff_C_mul]
  exact (MvPolynomial.smul_eq_C_mul
    ((maximalMinorWeightHom D n m f).coeff k) a).symm

lemma maximalMinorWeightHom_basis_coeff_eq_zero_of_lt_count
    {D : Type*} [CommRing D] {n m k : ℕ}
    (s : StandardMinorProductIndex (n + 1) m)
    (hk : k < maximalMinorCount s.1) :
    (maximalMinorWeightHom D n m
      (minorListPoly (D := D) s.1)).coeff k = 0 := by
  exact (Polynomial.X_pow_dvd_iff.mp
    (X_pow_maximalMinorCount_dvd_maximalMinorWeightHom_minorListPoly
      (D := D) s.1)) k hk

/-- For an arbitrary nonzero polynomial, any certified least
maximal-minor count in its standard-basis support is its tagged trailing
degree. -/
theorem natTrailingDegree_maximalMinorWeightHom_eq_of_isMinCount
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (f : GenericPoly D (n + 1) m) (_hf : f ≠ 0) (c : ℕ)
    (hc_exists : ∃ s ∈
      ((standardMinorProductBasis D (n + 1) m).repr f).support,
        maximalMinorCount s.1 = c)
    (hc_min : ∀ s ∈
      ((standardMinorProductBasis D (n + 1) m).repr f).support,
        c ≤ maximalMinorCount s.1) :
    (maximalMinorWeightHom D n m f).natTrailingDegree = c := by
  let b := standardMinorProductBasis D (n + 1) m
  let S := (b.repr f).support
  obtain ⟨s₀, hs₀S, hs₀c⟩ :
      ∃ s₀ ∈ S, maximalMinorCount s₀.1 = c := by
    simpa [b, S] using hc_exists
  have hc_le (s : StandardMinorProductIndex (n + 1) m) (hs : s ∈ S) :
      c ≤ maximalMinorCount s.1 := by
    exact hc_min s (by simpa [b, S] using hs)
  have hexpand :
      (b.repr f).sum (fun s a ↦ a • b s) = f := by
    rw [← Finsupp.linearCombination_apply, ← b.repr_symm_apply]
    exact b.repr.symm_apply_apply f
  have hcoeffExpand (k : ℕ) :
      (maximalMinorWeightHom D n m f).coeff k =
        ∑ s ∈ S, (b.repr f) s •
          (maximalMinorWeightHom D n m
            (minorListPoly (D := D) s.1)).coeff k := by
    conv_lhs => rw [← hexpand]
    change (Polynomial.lcoeff (StandardAuxPoly D (n + 1) m) k)
        (maximalMinorWeightHom D n m
          (∑ s ∈ S, (b.repr f) s • b s)) = _
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Polynomial.lcoeff_apply]
    rw [maximalMinorWeightHom_coeff_smul]
    change (b.repr f) s •
        (maximalMinorWeightHom D n m
          (standardMinorProductBasis D (n + 1) m s)).coeff k = _
    rw [standardMinorProductBasis_apply]
  have hQc : (maximalMinorWeightHom D n m f).coeff c ≠ 0 := by
    intro hzero
    have hrel :
        ∑ s ∈ S,
          (if maximalMinorCount s.1 = c then (b.repr f) s else 0) •
            (maximalMinorWeightHom D n m
              (minorListPoly (D := D) s.1)).coeff
                (maximalMinorCount s.1) = 0 := by
      rw [← hzero, hcoeffExpand c]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsc : maximalMinorCount s.1 = c
      · simp [hsc]
      · have hlt : c < maximalMinorCount s.1 :=
          lt_of_le_of_ne (hc_le s hs) (Ne.symm hsc)
        rw [maximalMinorWeightHom_basis_coeff_eq_zero_of_lt_count s hlt]
        simp [hsc]
    have hzeroCoeff :=
      (linearIndependent_iff'.mp
        (trailingCoeffSlice_standardBasis_linearIndependent
          (D := D) (n := n) (m := m)))
        S (fun s ↦ if maximalMinorCount s.1 = c then (b.repr f) s else 0)
        hrel s₀ hs₀S
    rw [if_pos hs₀c] at hzeroCoeff
    have hs₀ne : (b.repr f) s₀ ≠ 0 := by
      exact Finsupp.mem_support_iff.mp hs₀S
    exact hs₀ne hzeroCoeff
  have hQne : maximalMinorWeightHom D n m f ≠ 0 := by
    intro hQ
    rw [hQ, Polynomial.coeff_zero] at hQc
    exact hQc rfl
  apply le_antisymm
  · exact Polynomial.natTrailingDegree_le_of_ne_zero hQc
  · apply Polynomial.le_natTrailingDegree hQne
    intro k hk
    rw [hcoeffExpand]
    apply Finset.sum_eq_zero
    intro s hs
    have hks : k < maximalMinorCount s.1 :=
      lt_of_lt_of_le hk (hc_le s hs)
    rw [maximalMinorWeightHom_basis_coeff_eq_zero_of_lt_count s hks]
    simp

/-- Least maximal-minor count occurring in the standard-basis support;
defined as zero only for the zero polynomial. -/
noncomputable def standardBasisMaximalOrder
    (D : Type*) [CommRing D] [Nontrivial D] (n m : ℕ)
    (f : GenericPoly D (n + 1) m) : ℕ :=
  let b := standardMinorProductBasis D (n + 1) m
  let S := (b.repr f).support
  if hS : S.Nonempty then
    (S.image (fun s ↦ maximalMinorCount s.1)).min' (hS.image _)
  else 0

lemma natTrailingDegree_maximalMinorWeightHom_eq_standardBasisMaximalOrder
    {D : Type*} [CommRing D] [Nontrivial D] {n m : ℕ}
    (f : GenericPoly D (n + 1) m) (hf : f ≠ 0) :
    (maximalMinorWeightHom D n m f).natTrailingDegree =
      standardBasisMaximalOrder D n m f := by
  let b := standardMinorProductBasis D (n + 1) m
  let S := (b.repr f).support
  have hrepr : b.repr f ≠ 0 := by
    intro hzero
    apply hf
    have h := congrArg b.repr.symm hzero
    simpa using h
  have hS : S.Nonempty := Finsupp.support_nonempty_iff.mpr hrepr
  let C := S.image (fun s ↦ maximalMinorCount s.1)
  have hC : C.Nonempty := hS.image _
  let c := C.min' hC
  have hc_exists : ∃ s ∈
      ((standardMinorProductBasis D (n + 1) m).repr f).support,
        maximalMinorCount s.1 = c := by
    have hcC : c ∈ C := C.min'_mem hC
    rcases Finset.mem_image.mp hcC with ⟨s, hs, hsc⟩
    exact ⟨s, by simpa [b, S] using hs, hsc⟩
  have hc_min : ∀ s ∈
      ((standardMinorProductBasis D (n + 1) m).repr f).support,
        c ≤ maximalMinorCount s.1 := by
    intro s hs
    exact C.min'_le _ (Finset.mem_image.mpr
      ⟨s, by simpa [b, S] using hs, rfl⟩)
  have htrail :=
    natTrailingDegree_maximalMinorWeightHom_eq_of_isMinCount
      (D := D) f hf c hc_exists hc_min
  rw [htrail]
  simp [standardBasisMaximalOrder, b, S, hS, C, c]

lemma le_standardBasisMaximalOrder_iff
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (f : GenericPoly D (n + 1) m) (hf : f ≠ 0) :
    r ≤ standardBasisMaximalOrder D n m f ↔
      ∀ s ∈ ((standardMinorProductBasis D (n + 1) m).repr f).support,
        r ≤ maximalMinorCount s.1 := by
  let b := standardMinorProductBasis D (n + 1) m
  let S := (b.repr f).support
  have hrepr : b.repr f ≠ 0 := by
    intro hzero
    apply hf
    have h := congrArg b.repr.symm hzero
    simpa using h
  have hS : S.Nonempty := Finsupp.support_nonempty_iff.mpr hrepr
  let C := S.image (fun s ↦ maximalMinorCount s.1)
  have hC : C.Nonempty := hS.image _
  let c := C.min' hC
  have horder : standardBasisMaximalOrder D n m f = c := by
    simp [standardBasisMaximalOrder, b, S, hS, C, c]
  rw [horder]
  constructor
  · intro hrc s hs
    exact hrc.trans (C.min'_le _ (Finset.mem_image.mpr
      ⟨s, by simpa [b, S] using hs, rfl⟩))
  · intro hall
    have hcC : c ∈ C := C.min'_mem hC
    rcases Finset.mem_image.mp hcC with ⟨s, hs, hsc⟩
    rw [← hsc]
    exact hall s (by simpa [b, S] using hs)

lemma mem_maximalMinorIdealOver_pow_iff_repr_hasMaximalPrefix
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (hnm : n + 1 ≤ m) (f : GenericPoly D (n + 1) m) :
    f ∈ maximalMinorIdealOver D (n + 1) m hnm ^ r ↔
      ∀ s ∈ ((standardMinorProductBasis D (n + 1) m).repr f).support,
        HasMaximalPrefix r s.1 := by
  rw [← standardMaximalPrefixIdeal_eq_maximalMinorIdealOver_pow
    D hnm r]
  change f ∈ standardMaximalPrefixSubmodule D (n + 1) m r ↔ _
  rw [standardMaximalPrefixSubmodule_eq_standardBasisPrefixSubmodule
    D (Nat.succ_pos n) r]
  let b := standardMinorProductBasis D (n + 1) m
  let Q : Set (StandardMinorProductIndex (n + 1) m) :=
    {s | HasMaximalPrefix r s.1}
  change f ∈ Submodule.span D (b '' Q) ↔ _
  rw [Module.Basis.mem_span_image (b := b)]
  rfl

/-- Ideal-power membership is exactly the lower bound on the multiplicative
tagged order (with the zero polynomial handled separately). -/
theorem mem_maximalMinorIdealOver_pow_iff_trailingDegree
    {D : Type*} [CommRing D] [Nontrivial D] {n m r : ℕ}
    (hnm : n + 1 ≤ m) (f : GenericPoly D (n + 1) m) :
    f ∈ maximalMinorIdealOver D (n + 1) m hnm ^ r ↔
      f = 0 ∨ r ≤ (maximalMinorWeightHom D n m f).natTrailingDegree := by
  by_cases hf : f = 0
  · subst f
    simp
  · rw [mem_maximalMinorIdealOver_pow_iff_repr_hasMaximalPrefix
      hnm f]
    simp only [hf, false_or]
    rw [natTrailingDegree_maximalMinorWeightHom_eq_standardBasisMaximalOrder
      f hf]
    rw [le_standardBasisMaximalOrder_iff f hf]
    apply forall_congr'
    intro s
    apply imp_congr_right
    intro hs
    exact hasMaximalPrefix_iff_le_maximalMinorCount s.1 s.2.1

end LastYWeight

section YZLeftInverse

/-- Evaluate the auxiliary `Y` matrix at the identity and the auxiliary `Z`
matrix at the original generic matrix. -/
def standardYZEvalBack (D : Type*) [CommSemiring D] (n m : ℕ) :
    StandardAuxPoly D n m →ₐ[D] GenericPoly D n m :=
  MvPolynomial.bind₁ fun v ↦
    match ofLex (ofLex v).2 with
    | Sum.inl i =>
        if (ofLex v).1 = i then 1 else 0
    | Sum.inr j =>
        MvPolynomial.X ((ofLex v).1, j)

@[simp] lemma standardYZEvalBack_auxY
    {D : Type*} [CommSemiring D] {n m : ℕ} (i q : Fin n) :
    standardYZEvalBack D n m (auxY (D := D) i q) =
      if q = i then 1 else 0 := by
  simp [standardYZEvalBack, auxY, standardAuxYVar]
  -- port to Lean 4.33.1: the two sides now carry different `Decidable (q = i)` instances
  congr

@[simp] lemma standardYZEvalBack_auxZ
    {D : Type*} [CommSemiring D] {n m : ℕ} (q : Fin n) (j : Fin m) :
    standardYZEvalBack D n m (auxZ (D := D) q j) =
      MvPolynomial.X (q, j) := by
  simp [standardYZEvalBack, auxZ, standardAuxZVar]

@[simp] lemma standardYZEvalBack_auxYZEntry
    {D : Type*} [CommSemiring D] {n m : ℕ} (i : Fin n) (j : Fin m) :
    standardYZEvalBack D n m (auxYZEntry (D := D) i j) =
      MvPolynomial.X (i, j) := by
  simp [auxYZEntry]

/-- Evaluation at `Y = 1` is a left inverse to the `X ↦ YZ`
substitution. -/
lemma standardYZEvalBack_standardYZHom
    {D : Type*} [CommSemiring D] {n m : ℕ}
    (f : GenericPoly D n m) :
    standardYZEvalBack D n m (standardYZHom D n m f) = f := by
  have hhom :
      (standardYZEvalBack D n m).toRingHom.comp
          (standardYZHom D n m).toRingHom =
        RingHom.id (GenericPoly D n m) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [standardYZEvalBack, standardYZHom]
    · rintro ⟨i, j⟩
      simp
  exact RingHom.congr_fun hhom f

lemma standardYZHom_injective
    {D : Type*} [CommSemiring D] {n m : ℕ} :
    Function.Injective (standardYZHom D n m) :=
  Function.LeftInverse.injective
    (standardYZEvalBack_standardYZHom (D := D) (n := n) (m := m))

/-- Consequently the composite weight map is also injective. -/
lemma maximalMinorWeightHom_injective
    {D : Type*} [CommSemiring D] {n m : ℕ} :
    Function.Injective (maximalMinorWeightHom D n m) := by
  intro f g hfg
  apply standardYZHom_injective
  apply weightTagHom_injective (lastYVarWeight n m)
  exact hfg

end YZLeftInverse

section PrimeAndPrimary

/-- Strong cancellation detected by the tagged order: if the left factor is
not in the maximal-minor ideal, it can be cancelled modulo every power. -/
theorem mem_maximalMinorIdealOver_pow_of_mul_mem_of_not_mem
    {D : Type*} [CommRing D] [IsDomain D] {n m r : ℕ}
    (hnm : n + 1 ≤ m)
    {a b : GenericPoly D (n + 1) m}
    (hab : a * b ∈ maximalMinorIdealOver D (n + 1) m hnm ^ r)
    (ha : a ∉ maximalMinorIdealOver D (n + 1) m hnm) :
    b ∈ maximalMinorIdealOver D (n + 1) m hnm ^ r := by
  have ha_ne : a ≠ 0 := by
    intro ha0
    apply ha
    rw [ha0]
    exact Ideal.zero_mem _
  have hva : (maximalMinorWeightHom D n m a).natTrailingDegree = 0 := by
    have hnot : ¬(a = 0 ∨
        1 ≤ (maximalMinorWeightHom D n m a).natTrailingDegree) := by
      intro h
      have haPow := (mem_maximalMinorIdealOver_pow_iff_trailingDegree
        (D := D) (r := 1) hnm a).mpr h
      exact ha (by simpa using haPow)
    omega
  rcases (mem_maximalMinorIdealOver_pow_iff_trailingDegree
    (D := D) hnm (a * b)).mp hab with hab0 | habOrder
  · have hb0 : b = 0 := (mul_eq_zero.mp hab0).resolve_left ha_ne
    rw [hb0]
    exact Ideal.zero_mem _
  · by_cases hb0 : b = 0
    · rw [hb0]
      exact Ideal.zero_mem _
    · apply (mem_maximalMinorIdealOver_pow_iff_trailingDegree
        (D := D) hnm b).mpr
      right
      have hQa : maximalMinorWeightHom D n m a ≠ 0 :=
        fun hzero ↦ ha_ne (maximalMinorWeightHom_injective
          (by simpa using hzero))
      have hQb : maximalMinorWeightHom D n m b ≠ 0 :=
        fun hzero ↦ hb0 (maximalMinorWeightHom_injective
          (by simpa using hzero))
      have hmul :
          (maximalMinorWeightHom D n m (a * b)).natTrailingDegree =
            (maximalMinorWeightHom D n m a).natTrailingDegree +
              (maximalMinorWeightHom D n m b).natTrailingDegree := by
        rw [map_mul, Polynomial.natTrailingDegree_mul hQa hQb]
      rw [hmul, hva, zero_add] at habOrder
      exact habOrder

/-- The generic maximal-minor ideal over an integral domain is prime. -/
theorem maximalMinorIdealOver_isPrime
    {D : Type*} [CommRing D] [IsDomain D] {n m : ℕ}
    (hnm : n + 1 ≤ m) :
    (maximalMinorIdealOver D (n + 1) m hnm).IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro htop
    have h1 : (1 : GenericPoly D (n + 1) m) ∈
        maximalMinorIdealOver D (n + 1) m hnm := by
      simpa [htop]
    have h1pow : (1 : GenericPoly D (n + 1) m) ∈
        maximalMinorIdealOver D (n + 1) m hnm ^ 1 := by
      simpa using h1
    have hbad := (mem_maximalMinorIdealOver_pow_iff_trailingDegree
      (D := D) (r := 1) hnm 1).mp h1pow
    simpa [maximalMinorWeightHom] using hbad
  · intro x y hxy
    by_cases hx : x ∈ maximalMinorIdealOver D (n + 1) m hnm
    · exact Or.inl hx
    · right
      have hxypow : x * y ∈
          maximalMinorIdealOver D (n + 1) m hnm ^ 1 := by
        simpa using hxy
      simpa using
        (mem_maximalMinorIdealOver_pow_of_mul_mem_of_not_mem
          (D := D) (r := 1) hnm hxypow hx)

/-- Every positive power of the generic maximal-minor ideal is primary over
an integral domain. -/
theorem maximalMinorIdealOver_pow_isPrimary
    {D : Type*} [CommRing D] [IsDomain D] {n m r : ℕ}
    (hnm : n + 1 ≤ m) (hr : 0 < r) :
    (maximalMinorIdealOver D (n + 1) m hnm ^ r).IsPrimary := by
  let P := maximalMinorIdealOver D (n + 1) m hnm
  have hprime : P.IsPrime := maximalMinorIdealOver_isPrime (D := D) hnm
  have hradical : (P ^ r).radical = P := by
    rw [Ideal.radical_pow P (Nat.ne_of_gt hr), hprime.radical]
  rw [Ideal.isPrimary_iff]
  constructor
  · intro htop
    have h1 : (1 : GenericPoly D (n + 1) m) ∈ P ^ r := by
      simpa [P, htop]
    have hbad := (mem_maximalMinorIdealOver_pow_iff_trailingDegree
      (D := D) hnm 1).mp h1
    rcases hbad with hbad | hbad
    · exact one_ne_zero hbad
    · have :
        (maximalMinorWeightHom D n m
          (1 : GenericPoly D (n + 1) m)).natTrailingDegree = 0 := by
        simp [maximalMinorWeightHom]
      omega
  · intro x y hxy
    by_cases hy : y ∈ P
    · right
      rwa [hradical]
    · left
      apply mem_maximalMinorIdealOver_pow_of_mul_mem_of_not_mem
        (D := D) (r := r) hnm (a := y) (b := x) ?_ hy
      simpa [mul_comm] using hxy

/-- Paper-facing square case. -/
theorem maximalMinorIdealOver_sq_isPrimary
    {D : Type*} [CommRing D] [IsDomain D] {n m : ℕ}
    (hnm : n + 1 ≤ m) :
    (maximalMinorIdealOver D (n + 1) m hnm ^ 2).IsPrimary := by
  exact maximalMinorIdealOver_pow_isPrimary (D := D) hnm (by norm_num)

end PrimeAndPrimary

end GenericMaximalMinor

end
end
end

section
section
/-! Bridge from the mission's `maxMinorIdeal` to Kong et al.'s `maximalMinorIdealOver`
(finite-sample-information-monotones, `MaximalMinorWeight.lean`), and the saturation statement. -/

set_option autoImplicit false

namespace FiniteSampleDependence.Dev.FSDsatBridge

open FiniteSampleDependence.Rigidity GenericMaximalMinor

/-- A mission maximal minor, for a strictly increasing column choice, is the upstream maximal minor
of the corresponding order embedding. -/
lemma maxMinor_eq_maximalMinorPolyOver {n m : ℕ} (hnm : n ≤ m) (s : Fin n → Fin m)
    (hs : StrictMono s) :
    maxMinor s = maximalMinorPolyOver (D := ℝ) hnm (OrderEmbedding.ofStrictMono s hs) := rfl

/-- The two maximal-minor ideals agree. -/
lemma maxMinorIdeal_eq (n m : ℕ) (hnm : n ≤ m) :
    maxMinorIdeal n m = maximalMinorIdealOver ℝ n m hnm := by
  unfold maxMinorIdeal maximalMinorIdealOver
  congr 1
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨OrderEmbedding.ofStrictMono s hs, (maxMinor_eq_maximalMinorPolyOver hnm s hs).symm⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S, S.strictMono, maxMinor_eq_maximalMinorPolyOver hnm S S.strictMono⟩

theorem maximal_minor_saturation_dev {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    (maxMinorIdeal n m).IsPrime ∧
    (maxMinorIdeal n m ^ 2).IsPrimary ∧
    (maxMinorIdeal n m ^ 2).radical = maxMinorIdeal n m ∧
    ∀ a f : PolyRing n m, a ∉ maxMinorIdeal n m → a * f ∈ maxMinorIdeal n m ^ 2 →
      f ∈ maxMinorIdeal n m ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hp : (maxMinorIdeal (k + 1) m).IsPrime := by
    rw [maxMinorIdeal_eq _ _ hnm]; exact maximalMinorIdealOver_isPrime (D := ℝ) hnm
  have hq : (maxMinorIdeal (k + 1) m ^ 2).IsPrimary := by
    rw [maxMinorIdeal_eq _ _ hnm]; exact maximalMinorIdealOver_sq_isPrimary (D := ℝ) hnm
  have hrad : (maxMinorIdeal (k + 1) m ^ 2).radical = maxMinorIdeal (k + 1) m := by
    rw [Ideal.radical_pow _ (by norm_num), hp.radical]
  refine ⟨hp, hq, hrad, fun a f ha haf => ?_⟩
  rcases (Ideal.isPrimary_iff.1 hq).2 (mul_comm a f ▸ haf) with h | h
  · exact h
  · exact absurd (hrad ▸ h) ha

end FiniteSampleDependence.Dev.FSDsatBridge

end
end

section
open FiniteSampleDependence.Rigidity

/-- Proposition 4.3 (Maximal-minor saturation). For `2 ≤ n ≤ m`, the generic maximal-minor ideal
`I_n ⊆ ℝ[X_{iα}]` is prime and `I_n²` is `I_n`-primary (primary with radical `I_n`). In
particular, if `a ∉ I_n` and `a f ∈ I_n²`, then `f ∈ I_n²`. -/
theorem solution {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    (maxMinorIdeal n m).IsPrime ∧
    (maxMinorIdeal n m ^ 2).IsPrimary ∧
    (maxMinorIdeal n m ^ 2).radical = maxMinorIdeal n m ∧
    ∀ a f : PolyRing n m, a ∉ maxMinorIdeal n m → a * f ∈ maxMinorIdeal n m ^ 2 →
      f ∈ maxMinorIdeal n m ^ 2 := by
  apply FiniteSampleDependence.Dev.FSDsatBridge.maximal_minor_saturation_dev <;> assumption

end
