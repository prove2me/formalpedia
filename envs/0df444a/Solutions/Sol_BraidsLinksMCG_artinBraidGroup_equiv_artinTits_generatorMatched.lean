-- Prove2me | solution 1 for BraidsLinksMCG.artinBraidGroup_equiv_artinTits_generatorMatched
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:04:12.71954+00:00
-- url     : https://prove2.me/submissions/f0aa76c9-cfd1-44ea-87b8-48cf25b0018c

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinTitsA

open CoxeterSystem


/-!
# The platform braid group is the Artin–Tits group of type `A`

`BraidsLinksMCG.ArtinBraidGroup n` is presented by an explicit, hand-written relator set
`braidRels n`.  The standard object is the Artin–Tits (generalised braid) group of the
Coxeter matrix `CoxeterMatrix.A (n-1)`, presented by the relators
`braidWord M i i' * (braidWord M i' i)⁻¹` built from Mathlib's `CoxeterSystem.braidWord`.
This file proves the two presentations define the same group.

## Attribution

The route taken here — presenting the braid group as the Artin–Tits group of
`CoxeterMatrix.A` and reading its relations off `CoxeterSystem.braidWord` — follows the
development in `TauCeti/GroupTheory/Coxeter/Artin.lean` and
`TauCeti/GroupTheory/SpecificGroups/Braid.lean` of the Tau Ceti project,
<https://github.com/TauCetiProject/TauCeti> (Apache-2.0, "The Tau Ceti contributors").
No Tau Ceti source is reproduced here: `artinRelation` / `artinRelationsSet` below are
restated directly on Mathlib's Coxeter API, and every proof is written against Mathlib.
-/

open BraidsLinksMCG CoxeterSystem

namespace BraidBridge

variable {m : ℕ}

/-- The Artin–Tits relator of a Coxeter matrix: the two alternating words of length `M i i'`
in `i` and `i'`, one against the inverse of the other. -/
def artinRelation (M : CoxeterMatrix (Fin m)) (i i' : Fin m) : FreeGroup (Fin m) :=
  ((braidWord M i i').map FreeGroup.of).prod *
    (((braidWord M i' i).map FreeGroup.of).prod)⁻¹

/-- The set of all Artin–Tits relators of `M`. -/
def artinRelationsSet (M : CoxeterMatrix (Fin m)) : Set (FreeGroup (Fin m)) :=
  Set.range (Function.uncurry (artinRelation M))

theorem artinRelation_mem (M : CoxeterMatrix (Fin m)) (i i' : Fin m) :
    artinRelation M i i' ∈ artinRelationsSet M := ⟨(i, i'), rfl⟩

/-- The Artin–Tits group of type `A` on `n` strands. -/
abbrev ArtinTits (n : ℕ) := PresentedGroup (artinRelationsSet (CoxeterMatrix.A (n - 1)))

/-! ### Computing the two relevant alternating words -/

theorem braidWord_two (M : CoxeterMatrix (Fin m)) (i i' : Fin m) (h : M i i' = 2) :
    braidWord M i i' = [i, i'] := by
  simp [braidWord, h, alternatingWord]

theorem braidWord_three (M : CoxeterMatrix (Fin m)) (i i' : Fin m) (h : M i i' = 3) :
    braidWord M i i' = [i', i, i'] := by
  simp [braidWord, h, alternatingWord]

/-! ### The entries of `CoxeterMatrix.A` -/

theorem A_apply_of_dist (i i' : Fin m) (h : 2 ≤ ((i : ℤ) - (i' : ℤ)).natAbs) :
    CoxeterMatrix.A m i i' = 2 := by
  have hne : i ≠ i' := by rintro rfl; simp at h
  have h1 : ¬ ((i' : ℕ) + 1 = i ∨ (i : ℕ) + 1 = i') := by omega
  simp [CoxeterMatrix.A, hne, h1]

theorem A_apply_of_succ (i i' : Fin m) (h : (i' : ℕ) = (i : ℕ) + 1) :
    CoxeterMatrix.A m i i' = 3 := by
  have hne : i ≠ i' := by
    rintro rfl; omega
  simp [CoxeterMatrix.A, hne, h]



theorem A_apply_of_pred (i i' : Fin m) (h : (i : ℕ) = (i' : ℕ) + 1) :
    CoxeterMatrix.A m i i' = 3 := by
  have hne : i ≠ i' := by rintro rfl; omega
  simp [CoxeterMatrix.A, hne, h]

/-! ### The two relator sets have the same normal closure -/

/-- `FreeGroup.lift PresentedGroup.of` is the quotient map. -/
theorem lift_of_eq_mk {α : Type*} (rels : Set (FreeGroup α)) :
    FreeGroup.lift (PresentedGroup.of : α → PresentedGroup rels) = PresentedGroup.mk rels := by
  apply FreeGroup.ext_hom
  intro x
  simp [PresentedGroup.of]

/-- Every hand-written platform relator is an Artin–Tits relator of `CoxeterMatrix.A`. -/
theorem braidRels_subset (n : ℕ) :
    braidRels n ⊆ artinRelationsSet (CoxeterMatrix.A (n - 1)) := by
  rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · -- commuting relator: it is `artinRelation _ i j`, since `A i j = 2`
    refine ⟨(i, j), ?_⟩
    have h2 : CoxeterMatrix.A (n - 1) i j = 2 := A_apply_of_dist i j hij
    have h2' : CoxeterMatrix.A (n - 1) j i = 2 :=
      A_apply_of_dist j i (by omega)
    simp only [Function.uncurry, artinRelation, braidWord_two _ i j h2,
      braidWord_two _ j i h2', List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_inv_rev]
    group
  · -- braid relator: it is `artinRelation _ j i`, since `A j i = 3`
    refine ⟨(j, i), ?_⟩
    have h3 : CoxeterMatrix.A (n - 1) j i = 3 := A_apply_of_pred j i hij
    have h3' : CoxeterMatrix.A (n - 1) i j = 3 := A_apply_of_succ i j hij
    simp only [Function.uncurry, artinRelation, braidWord_three _ j i h3,
      braidWord_three _ i j h3', List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_inv_rev]
    group

theorem braidWord_one (M : CoxeterMatrix (Fin m)) (i i' : Fin m) (h : M i i' = 1) :
    braidWord M i i' = [i'] := by
  simp [braidWord, h, alternatingWord]

/-- Conversely, every Artin–Tits relator of `CoxeterMatrix.A` dies in the platform group. -/
theorem artinRels_map_one (n : ℕ) :
    ∀ r ∈ artinRelationsSet (CoxeterMatrix.A (n - 1)),
      FreeGroup.lift (PresentedGroup.of : Fin (n - 1) → ArtinBraidGroup n) r = 1 := by
  rintro r ⟨⟨i, j⟩, rfl⟩
  rw [lift_of_eq_mk]
  show PresentedGroup.mk (braidRels n) (artinRelation _ i j) = 1
  rcases eq_or_ne i j with rfl | hne
  · have h1 : CoxeterMatrix.A (n - 1) i i = 1 := by simp [CoxeterMatrix.A]
    have : artinRelation (CoxeterMatrix.A (n - 1)) i i = 1 := by
      simp [artinRelation, braidWord_one _ i i h1]
    rw [this, map_one]
  · have hij : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
    by_cases hsucc : (j : ℕ) = (i : ℕ) + 1
    · -- adjacent, `j = i + 1`: the relator is the inverse of the platform's
      have h3 : CoxeterMatrix.A (n - 1) i j = 3 := A_apply_of_succ i j hsucc
      have h3' : CoxeterMatrix.A (n - 1) j i = 3 := A_apply_of_pred j i hsucc
      have heq : artinRelation (CoxeterMatrix.A (n - 1)) i j =
          (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
            (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹)⁻¹ := by
        simp only [artinRelation, braidWord_three _ i j h3, braidWord_three _ j i h3',
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        group
      rw [heq, map_inv, PresentedGroup.one_of_mem (Or.inr ⟨i, j, hsucc, rfl⟩), inv_one]
    · by_cases hpred : (i : ℕ) = (j : ℕ) + 1
      · -- adjacent, `i = j + 1`: the relator is the platform's with roles swapped
        have h3 : CoxeterMatrix.A (n - 1) j i = 3 := A_apply_of_succ j i hpred
        have h3' : CoxeterMatrix.A (n - 1) i j = 3 := A_apply_of_pred i j hpred
        have heq : artinRelation (CoxeterMatrix.A (n - 1)) i j =
            FreeGroup.of j * FreeGroup.of i * FreeGroup.of j *
              (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i)⁻¹ := by
          simp only [artinRelation, braidWord_three _ i j h3', braidWord_three _ j i h3,
            List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          group
        rw [heq, PresentedGroup.one_of_mem (Or.inr ⟨j, i, hpred, rfl⟩)]
      · -- far apart: the relator is the platform's commuting relator
        have hd : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs := by omega
        have h2 : CoxeterMatrix.A (n - 1) i j = 2 := A_apply_of_dist i j hd
        have h2' : CoxeterMatrix.A (n - 1) j i = 2 := A_apply_of_dist j i (by omega)
        have heq : artinRelation (CoxeterMatrix.A (n - 1)) i j =
            FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹ := by
          simp only [artinRelation, braidWord_two _ i j h2, braidWord_two _ j i h2',
            List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          group
        rw [heq, PresentedGroup.one_of_mem (Or.inl ⟨i, j, hd, rfl⟩)]

/-! ### The isomorphism

`ArtinBraidGroup n` is a `def` carrying its own `Group` instance, which does not match the
`PresentedGroup` instance at `implicit` transparency; the maps are therefore built on
`PresentedGroup (braidRels n)` and transported at the end (the two are definitionally equal). -/

theorem braidRels_map_one (n : ℕ) :
    ∀ r ∈ braidRels n,
      FreeGroup.lift (PresentedGroup.of : Fin (n - 1) → ArtinTits n) r = 1 := by
  intro r hr
  rw [lift_of_eq_mk]
  exact PresentedGroup.one_of_mem (braidRels_subset n hr)

/-- The platform braid group maps to the Artin–Tits group of type `A`. -/
def toArtinTits (n : ℕ) : PresentedGroup (braidRels n) →* ArtinTits n :=
  PresentedGroup.toGroup (braidRels_map_one n)

/-- ... and back. -/
def ofArtinTits (n : ℕ) : ArtinTits n →* PresentedGroup (braidRels n) :=
  PresentedGroup.toGroup (artinRels_map_one n)

@[simp] theorem toArtinTits_of (n : ℕ) (i : Fin (n - 1)) :
    toArtinTits n (PresentedGroup.of i) = PresentedGroup.of i :=
  PresentedGroup.toGroup.of _

@[simp] theorem ofArtinTits_of (n : ℕ) (i : Fin (n - 1)) :
    ofArtinTits n (PresentedGroup.of i) = PresentedGroup.of i :=
  PresentedGroup.toGroup.of _

theorem of_comp_to (n : ℕ) :
    (ofArtinTits n).comp (toArtinTits n) = MonoidHom.id (PresentedGroup (braidRels n)) :=
  PresentedGroup.ext (by
    intro x
    simp only [MonoidHom.comp_apply, toArtinTits_of, ofArtinTits_of, MonoidHom.id_apply])

theorem to_comp_of (n : ℕ) :
    (toArtinTits n).comp (ofArtinTits n) = MonoidHom.id (ArtinTits n) :=
  PresentedGroup.ext (by
    intro x
    simp only [MonoidHom.comp_apply, ofArtinTits_of, toArtinTits_of, MonoidHom.id_apply])

/-- **The bridge.** The platform's hand-written presentation of the braid group agrees with
the standard Artin–Tits presentation of type `A`, matching the generators. -/
def equiv (n : ℕ) : PresentedGroup (braidRels n) ≃* ArtinTits n where
  toFun := toArtinTits n
  invFun := ofArtinTits n
  left_inv := fun x => congrArg (fun f => f x) (of_comp_to n)
  right_inv := fun x => congrArg (fun f => f x) (to_comp_of n)
  map_mul' := map_mul _

@[simp] theorem equiv_of (n : ℕ) (i : Fin (n - 1)) :
    equiv n (PresentedGroup.of i) = PresentedGroup.of i := toArtinTits_of n i

/-- The platform's `ArtinBraidGroup` is the Artin–Tits group of type `A`. -/
theorem nonempty_equiv (n : ℕ) : Nonempty (ArtinBraidGroup n ≃* ArtinTits n) := ⟨equiv n⟩

end BraidBridge

theorem solution (n : ℕ) :
    ∃ e : BraidsLinksMCG.ArtinBraidGroup n ≃* BraidsLinksMCG.artinTitsA n,
      ∀ i : Fin (n - 1), e (BraidsLinksMCG.sigma i) = PresentedGroup.of i :=
  ⟨BraidBridge.equiv n, fun i => BraidBridge.equiv_of n i⟩

