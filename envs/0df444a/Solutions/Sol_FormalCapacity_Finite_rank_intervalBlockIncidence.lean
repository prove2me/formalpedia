-- Prove2me | solution 1 for FormalCapacity.Finite.rank_intervalBlockIncidence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-07T18:12:31.635128+00:00
-- url     : https://prove2.me/submissions/83662ffa-d569-4510-8dbe-b31c168fc8f9

import Mathlib
import Definitions.Def_capacityFinitePartitions
import Definitions.Def_capacityBlockIncidence
import Definitions.Def_capacityFourLabelAtoms
import Definitions.Def_capacityIntervalIncidence
import Definitions.Def_capacityFourLabelCompositions

set_option autoImplicit false

/-!
# Finite partitions and their block-incidence rows

We use mathlib's `Finpartition` representation.  The key test partition has
one prescribed nonempty block `S` and singleton blocks outside `S`.
-/

namespace FormalCapacity.Finite

open scoped BigOperators
open Finset

variable {α R : Type*} [Fintype α] [DecidableEq α]















end FormalCapacity.Finite


/-!
# Rank of first-order block incidence

This file upgrades the row-relation characterization in `Partition.lean` to
the finite-dimensional rank formula `2^n - n`.
-/

namespace FormalCapacity.Finite

open scoped BigOperators
open Finset Module

variable {α : Type*} [Fintype α] [DecidableEq α]





























theorem labelSum_ne_zero [Nonempty α] : labelSum (α := α) ≠ 0 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty α)
  intro h
  have hfun := LinearMap.congr_fun h (fun j ↦ if j = i then (1 : ℚ) else 0)
  simp [labelSum] at hfun









end FormalCapacity.Finite


/-!
# The four-label correlation obstruction

This file kernel-checks the signed square

`12|34 + 1|2|3|4 = 1|2|34 + 12|3|4`

at every block-incidence coordinate.  The four atoms are represented by
their finite sets of blocks.  `n4Atom_isPartition` verifies that each label
belongs to exactly one nonempty block, so this concrete representation does
not hide a partition-validity assumption.
-/

namespace FormalCapacity.Finite

open Finset







/-- A finite block family is a partition certificate when it has no empty
block and every label occurs in exactly one block. -/
def HasPartitionCertificate (bs : Finset (Finset Label4)) : Prop :=
  ∅ ∉ bs ∧ ∀ i : Label4, #(bs.filter fun B ↦ i ∈ B) = 1

/-- All four atoms really are partitions of the four labels. -/
theorem n4Atom_isPartition (P : N4Atom) :
    HasPartitionCertificate P.blocks := by
  cases P <;> constructor
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide









/-- Their two supports are disjoint, hence the laws are different. -/
theorem n4_twoAtomSupports_disjoint :
    Disjoint ({N4Atom.plusCoarse, .plusDiscrete} : Finset N4Atom)
      ({N4Atom.minusLeft, .minusRight} : Finset N4Atom) := by
  decide

























end FormalCapacity.Finite


/-!
# Exact rank for interval partitions

Rows are nonempty intervals of Fin n, represented by their ordered
endpoints. Columns are genuine Finpartitions all of whose blocks carry an
endpoint certificate. This realizes compositions without choosing a cut-set
encoding.
-/

namespace FormalCapacity.Finite

open scoped BigOperators
open Finset Module Set





@[simp]
theorem IntervalEndpoint.left_mem {n : ℕ} (I : IntervalEndpoint n) :
    I.1 ∈ I.toFinset := mem_Icc.mpr ⟨le_rfl, I.2.2⟩

theorem IntervalEndpoint.toFinset_nonempty {n : ℕ} (I : IntervalEndpoint n) :
    I.toFinset.Nonempty := ⟨I.1, I.left_mem⟩



theorem IntervalEndpoint.toFinset_injective {n : ℕ} :
    Function.Injective (@IntervalEndpoint.toFinset n) := by
  rintro ⟨i, j, hij⟩ ⟨k, l, hkl⟩ hEq
  simp only [IntervalEndpoint.toFinset] at hEq
  have hi_mem : i ∈ Finset.Icc i j := mem_Icc.mpr ⟨le_rfl, hij⟩
  have hk_mem : k ∈ Finset.Icc k l := mem_Icc.mpr ⟨le_rfl, hkl⟩
  have hj_mem : j ∈ Finset.Icc i j := mem_Icc.mpr ⟨hij, le_rfl⟩
  have hl_mem : l ∈ Finset.Icc k l := mem_Icc.mpr ⟨hkl, le_rfl⟩
  have hki : k ≤ i := (mem_Icc.mp (hEq ▸ hi_mem)).1
  have hik : i ≤ k := (mem_Icc.mp (hEq.symm ▸ hk_mem)).1
  have hjl : j ≤ l := (mem_Icc.mp (hEq ▸ hj_mem)).2
  have hlj : l ≤ j := (mem_Icc.mp (hEq.symm ▸ hl_mem)).2
  have hi : i = k := le_antisymm hik hki
  have hj : j = l := le_antisymm hjl hlj
  subst k
  subst l
  rfl

/-- The elementary triangular-number identity used in the row count. -/
theorem sum_fin_card_sub_val (n : ℕ) :
    (univ : Finset (Fin n)).sum (fun i ↦ n - i.val) = n.choose 2 + n := by
  rw [Fin.sum_univ_eq_sum_range]
  calc
    (range n).sum (fun i ↦ n - i) =
        (range n).sum (fun i ↦ (n - 1 - i) + 1) := by
      apply sum_congr rfl
      intro i hi
      have hin : i < n := mem_range.mp hi
      omega
    _ = (range n).sum (fun i ↦ i + 1) := by
      simpa only [] using Finset.sum_range_reflect (fun i ↦ i + 1) n
    _ = (range n).sum (fun i ↦ i) + (range n).sum (fun _i ↦ 1) := by
      simpa only [] using Finset.sum_add_distrib
    _ = n.choose 2 + n := by
      rw [Finset.sum_range_id, Nat.choose_two_right]
      simp

/-- There are choose(n,2)+n nonempty intervals in an n-element chain. -/
theorem card_intervalEndpoint (n : ℕ) :
    Fintype.card (IntervalEndpoint n) = n.choose 2 + n := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_Ici, Fin.card_Ici]
  change (univ : Finset (Fin n)).sum (fun i ↦ n - i.val) = n.choose 2 + n
  exact sum_fin_card_sub_val n



/-- The composition having one prescribed interval and singleton blocks
outside it. -/
def isolateInterval {n : ℕ} (I : IntervalEndpoint n) : IntervalPartition n where
  partition := isolateBlock I.toFinset I.toFinset_nonempty
  interval := by
    intro B hB
    have hB' : B ∈ isolateBlockParts I.toFinset := by
      simpa only [isolateBlock_parts] using hB
    unfold isolateBlockParts at hB'
    by_cases hEq : B = I.toFinset
    · exact ⟨I, hEq.symm⟩
    · have hImage : B ∈
          ((Finset.univ : Finset (Fin n)) \ I.toFinset).image (fun i ↦ ({i} : Finset (Fin n))) :=
        (mem_insert.mp hB').resolve_left hEq
      obtain ⟨i, _, hi⟩ := mem_image.mp hImage
      refine ⟨⟨i, ⟨i, by simp⟩⟩, ?_⟩
      simpa [IntervalEndpoint.toFinset] using hi

/-- The discrete composition. -/
def discreteIntervalPartition (n : ℕ) : IntervalPartition n where
  partition := ⊥
  interval := by
    intro B hB
    rw [Finpartition.mem_bot_iff] at hB
    obtain ⟨i, _, hB⟩ := hB
    exact ⟨⟨i, ⟨i, by simp⟩⟩, by simpa [IntervalEndpoint.toFinset] using hB⟩

/-- The singleton endpoint interval. -/
def singletonInterval {n : ℕ} (i : Fin n) : IntervalEndpoint n :=
  ⟨i, ⟨i, by simp⟩⟩

@[simp]
theorem singletonInterval_toFinset {n : ℕ} (i : Fin n) :
    (singletonInterval i).toFinset = {i} := by
  simp [singletonInterval, IntervalEndpoint.toFinset]



theorem extendIntervalCoeff_toFinset {n : ℕ}
    (c : IntervalEndpoint n → ℚ) (I : IntervalEndpoint n) :
    extendIntervalCoeff c I.toFinset = c I := by
  classical
  unfold extendIntervalCoeff
  split_ifs with h
  · have hEq : Classical.choose h = I :=
      IntervalEndpoint.toFinset_injective (Classical.choose_spec h)
    rw [hEq]
  · exact (h ⟨I, rfl⟩).elim

@[simp]
theorem extendIntervalCoeff_singleton {n : ℕ}
    (c : IntervalEndpoint n → ℚ) (i : Fin n) :
    extendIntervalCoeff c {i} = c (singletonInterval i) := by
  rw [← singletonInterval_toFinset i, extendIntervalCoeff_toFinset]







/-- The interval-row nullspace again consists exactly of zero-sum modular
singleton potentials. -/
theorem mem_ker_intervalBlockIncidenceTranspose_iff {n : ℕ}
    (c : IntervalEndpoint n → ℚ) :
    c ∈ (intervalBlockIncidenceTranspose n).ker ↔
      (∀ I : IntervalEndpoint n,
        c I = ∑ i ∈ I.toFinset, c (singletonInterval i)) ∧
      (∑ i : Fin n, c (singletonInterval i)) = 0 := by
  constructor
  · intro hc
    have hzero : intervalBlockIncidenceTranspose n c = 0 := hc
    have hdiscrete :
        blockRowSum (extendIntervalCoeff c)
          (discreteIntervalPartition n).partition = 0 :=
      congrFun hzero (discreteIntervalPartition n)
    change blockRowSum (extendIntervalCoeff c)
      (⊥ : Finpartition (univ : Finset (Fin n))) = 0 at hdiscrete
    simp only [blockRowSum, Finpartition.parts_bot] at hdiscrete
    rw [sum_map] at hdiscrete
    simp only [Function.Embedding.coeFn_mk, extendIntervalCoeff_singleton] at hdiscrete
    constructor
    · intro I
      have hisolate :
          blockRowSum (extendIntervalCoeff c) (isolateInterval I).partition = 0 :=
        congrFun hzero (isolateInterval I)
      change blockRowSum (extendIntervalCoeff c)
        (isolateBlock I.toFinset I.toFinset_nonempty) = 0 at hisolate
      have hnot : I.toFinset ∉
          ((univ : Finset (Fin n)) \ I.toFinset).image singleton := by
        intro h
        obtain ⟨i, hi, hEq⟩ := mem_image.mp h
        have hi_not : i ∉ I.toFinset := by simpa using hi
        have hi_mem : i ∈ I.toFinset := by
          have : i ∈ ({i} : Finset (Fin n)) := mem_singleton_self i
          rwa [hEq] at this
        exact hi_not hi_mem
      simp only [blockRowSum, isolateBlock_parts, isolateBlockParts,
        sum_insert hnot] at hisolate
      rw [extendIntervalCoeff_toFinset] at hisolate
      have hinj : Set.InjOn (fun i : Fin n ↦ ({i} : Finset (Fin n)))
          (↑((univ : Finset (Fin n)) \ I.toFinset) : Set (Fin n)) := by
        intro i _ j _ h
        exact singleton_injective h
      rw [sum_image hinj] at hisolate
      simp only [extendIntervalCoeff_singleton] at hisolate

      have hunion :
          I.toFinset ∪ ((univ : Finset (Fin n)) \ I.toFinset) =
            (Finset.univ : Finset (Fin n)) := by
        ext i
        simp
      have hdisj :
          Disjoint I.toFinset ((univ : Finset (Fin n)) \ I.toFinset) :=
        Finset.disjoint_sdiff
      have hsplit :
          (∑ i : Fin n, c (singletonInterval i)) =
            (∑ i ∈ I.toFinset, c (singletonInterval i)) +
              ∑ i ∈ ((univ : Finset (Fin n)) \ I.toFinset),
                c (singletonInterval i) := by
        rw [← sum_union hdisj, hunion]
      rw [hsplit] at hdiscrete
      exact (eq_neg_of_add_eq_zero_left hisolate).trans
        (neg_eq_of_add_eq_zero_left hdiscrete)
    · simpa only [sum_attach] using hdiscrete
  · rintro ⟨hmod, hsum⟩
    rw [LinearMap.mem_ker]
    funext P
    change blockRowSum (extendIntervalCoeff c) P.partition = 0
    have hpoint : ∀ B ∈ P.partition.parts,
        extendIntervalCoeff c B =
          ∑ i ∈ B, c (singletonInterval i) := by
      intro B hB
      obtain ⟨I, hI⟩ := P.interval B hB
      subst B
      rw [extendIntervalCoeff_toFinset, hmod]
    simp only [blockRowSum]
    calc
      (∑ B ∈ P.partition.parts, extendIntervalCoeff c B) =
          ∑ B ∈ P.partition.parts,
            (∑ i ∈ B, c (singletonInterval i)) := by
        apply sum_congr rfl
        exact hpoint
      _ = 0 := sum_singletons_rowRelation
        (fun i ↦ c (singletonInterval i)) hsum P.partition

/-- A label potential evaluated on each endpoint interval. -/
def intervalModularPotential (n : ℕ) :
    (Fin n → ℚ) →ₗ[ℚ] (IntervalEndpoint n → ℚ) where
  toFun a I := ∑ i ∈ I.toFinset, a i
  map_add' a b := by
    ext I
    simp [Finset.sum_add_distrib]
  map_smul' r a := by
    ext I
    simp [Finset.mul_sum]

/-- Restrict the modular-potential map to zero-sum labels and the interval
incidence kernel. -/
noncomputable def intervalPotentialToKernel (n : ℕ) :
    (labelSum (α := Fin n)).ker →ₗ[ℚ]
      (intervalBlockIncidenceTranspose n).ker where
  toFun a := ⟨intervalModularPotential n a.1, by
    apply (mem_ker_intervalBlockIncidenceTranspose_iff _).2
    constructor
    · intro I
      simp [intervalModularPotential]
    · simpa [intervalModularPotential, labelSum] using a.2⟩
  map_add' a b := by
    ext I
    simp [intervalModularPotential, Finset.sum_add_distrib]
  map_smul' r a := by
    ext I
    simp [intervalModularPotential, Finset.mul_sum]

theorem intervalPotentialToKernel_bijective (n : ℕ) :
    Function.Bijective (intervalPotentialToKernel n) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext i
    have hi := congrFun (congrArg Subtype.val hab) (singletonInterval i)
    simpa [intervalPotentialToKernel, intervalModularPotential] using hi
  · intro c
    let a : Fin n → ℚ := fun i ↦ c.1 (singletonInterval i)
    have hc := (mem_ker_intervalBlockIncidenceTranspose_iff c.1).1 c.2
    have ha : a ∈ (labelSum (α := Fin n)).ker := by
      simpa [LinearMap.mem_ker, labelSum, a] using hc.2
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    funext I
    simpa [intervalPotentialToKernel, intervalModularPotential, a] using (hc.1 I).symm

/-- The interval-incidence row kernel is linearly equivalent to zero-sum
label potentials. -/
noncomputable def intervalIncidenceKernelEquivZeroSum (n : ℕ) :
    (labelSum (α := Fin n)).ker ≃ₗ[ℚ]
      (intervalBlockIncidenceTranspose n).ker :=
  LinearEquiv.ofBijective (intervalPotentialToKernel n)
    (intervalPotentialToKernel_bijective n)

/-- The interval-row nullspace has dimension n-1. -/
theorem finrank_ker_intervalBlockIncidenceTranspose (n : ℕ) (hn : 0 < n) :
    finrank ℚ (intervalBlockIncidenceTranspose n).ker = n - 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← (intervalIncidenceKernelEquivZeroSum n).finrank_eq]
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (labelSum_ne_zero (α := Fin n))
  rw [Module.finrank_pi] at h
  simp only [Fintype.card_fin] at h
  omega





end FormalCapacity.Finite


/-!
# The unique hidden direction on four ordered labels

There are eight interval partitions (compositions) of four ordered labels.
This file writes all eight down and proves directly that the kernel of their
first-order interval-block incidence map is the single line generated by

`12|34 + 1|2|3|4 - 1|2|34 - 12|3|4`.

Thus the signed square from `N4.lean` is not merely an example: among signed
laws on all four-label compositions it is the unique invisible direction,
up to scale.
-/

namespace FormalCapacity.Finite

open Finset





/-- The eight displayed block families are genuine partitions. -/
theorem composition4_isPartition (P : Composition4) :
    HasPartitionCertificate P.blocks := by
  cases P <;> constructor
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide
  · decide
  · intro i; fin_cases i <;> decide









/-- The square is a genuinely nonzero signed law. -/
theorem composition4Square_ne_zero : composition4Square ≠ 0 := by
  intro h
  have := congrFun h Composition4.halves
  norm_num [composition4Square] at this





end FormalCapacity.Finite


/-!
# Finite merge generators and their polar

For a finite label set, an elementary early-minus-late merge replaces a
pairwise-disjoint family of nonempty blocks by its union.  This file proves
the exact pairing formula, identifies the generator-level polar with
coarsening superadditivity, constructs the canonical modular normalization,
and supplies the strictly positive block-count functional used to prove
pointedness of the generated cone.
-/

namespace FormalCapacity.Finite

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]



















































end FormalCapacity.Finite


/-!
# Exact rank for interval partitions

Rows are nonempty intervals of Fin n, represented by their ordered
endpoints. Columns are genuine Finpartitions all of whose blocks carry an
endpoint certificate. This realizes compositions without choosing a cut-set
encoding.
-/

open FormalCapacity.Finite

open scoped BigOperators
open Finset Module Set

theorem solution (n : ℕ) (hn : 0 < n) :
    finrank ℚ (intervalBlockIncidenceTranspose n).range = n.choose 2 + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (intervalBlockIncidenceTranspose n)
  rw [finrank_ker_intervalBlockIncidenceTranspose n hn,
    Module.finrank_pi, card_intervalEndpoint] at h
  omega
