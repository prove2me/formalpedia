-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeComponentCycleOrderOfIsCyclesComponent
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:12:15.490034+00:00
-- url     : https://prove2.me/submissions/8cde0aa1-8b10-423f-a513-b6098220e5dd

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

set_option maxRecDepth 100000

/-- A three-residue source assembly for a path of two cross edges.  The
source has residual triples on A, B, and C and two exceptional triples.  Its
edge hypotheses are deliberately expressed only through an explicit target
bijection; the component-coordinate specialization below supplies such a
bijection from three cyclic orders. -/
theorem R03SP01ThreeComponentZeroOneTwoSourceAssembly
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (a b c : Nat)
    (target :
      (((Fin a × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3)))) ≃
        (A ⊕ (B ⊕ C))))
    (hA : ∀ i : Fin a,
      G.Adj (target (Sum.inl (i, (0 : Fin 3))))
        (target (Sum.inl (i, (1 : Fin 3)))) ∧
      G.Adj (target (Sum.inl (i, (1 : Fin 3))))
        (target (Sum.inl (i, (2 : Fin 3)))))
    (hB : ∀ i : Fin b,
      G.Adj (target (Sum.inr (Sum.inl (i, (0 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (1 : Fin 3))))) ∧
      G.Adj (target (Sum.inr (Sum.inl (i, (1 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (2 : Fin 3))))))
    (hC : ∀ i : Fin c,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3))))))
        (target
          (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))) ∧
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))
        (target
          (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3)))))))
    (hExc01 : ∀ i : Fin 2,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))))
    (hExc12 : ∀ i : Fin 2,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3))))))) :
    Nonempty (P3Factor G) := by
  let blockSum : Fin (a + (b + (c + 2))) ≃
      Fin a ⊕ (Fin b ⊕ (Fin c ⊕ Fin 2)) :=
    finSumFinEquiv.symm.trans
      (Equiv.sumCongr (Equiv.refl (Fin a))
        (finSumFinEquiv.symm.trans
          (Equiv.sumCongr (Equiv.refl (Fin b))
            finSumFinEquiv.symm)))
  let dA : (Fin a ⊕ (Fin b ⊕ (Fin c ⊕ Fin 2))) × Fin 3 ≃
      (Fin a × Fin 3) ⊕ ((Fin b ⊕ (Fin c ⊕ Fin 2)) × Fin 3) :=
    Equiv.sumProdDistrib (Fin a) (Fin b ⊕ (Fin c ⊕ Fin 2)) (Fin 3)
  let dB : (Fin b ⊕ (Fin c ⊕ Fin 2)) × Fin 3 ≃
      (Fin b × Fin 3) ⊕ ((Fin c ⊕ Fin 2) × Fin 3) :=
    Equiv.sumProdDistrib (Fin b) (Fin c ⊕ Fin 2) (Fin 3)
  let dC : (Fin c ⊕ Fin 2) × Fin 3 ≃
      (Fin c × Fin 3) ⊕ (Fin 2 × Fin 3) :=
    Equiv.sumProdDistrib (Fin c) (Fin 2) (Fin 3)
  let distributed :
      (Fin a ⊕ (Fin b ⊕ (Fin c ⊕ Fin 2))) × Fin 3 ≃
      ((Fin a × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3)))) :=
    dA.trans (Equiv.sumCongr (Equiv.refl (Fin a × Fin 3))
      (dB.trans (Equiv.sumCongr (Equiv.refl (Fin b × Fin 3)) dC)))
  let blockToSource :
      (Fin (a + (b + (c + 2))) × Fin 3) ≃
      ((Fin a × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3)))) :=
    (blockSum.prodCongr (Equiv.refl (Fin 3))).trans distributed
  let place : (Fin (a + (b + (c + 2))) × Fin 3) ≃
      (A ⊕ (B ⊕ C)) := blockToSource.trans target
  refine ⟨{
    blockCount := a + (b + (c + 2))
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have h := (hA i).1
      simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
        Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
        finProdFinEquiv] using h
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have h := (hB i).1
        simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
          Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
          finProdFinEquiv] using h
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · have h := (hC i).1
          simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
            Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
            finProdFinEquiv] using h
        · fin_cases i
          · have h := hExc01 0
            simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
              Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
              finProdFinEquiv] using h
          · have h := hExc01 1
            simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
              Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
              finProdFinEquiv] using h
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have h := (hA i).2
      simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
        Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
        finProdFinEquiv] using h
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have h := (hB i).2
        simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
          Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
          finProdFinEquiv] using h
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · have h := (hC i).2
          simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
            Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
            finProdFinEquiv] using h
        · fin_cases i
          · have h := hExc12 0
            simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
              Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
              finProdFinEquiv] using h
          · have h := hExc12 1
            simpa [place, blockToSource, blockSum, distributed, dA, dB, dC,
              Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
              finProdFinEquiv] using h

#print axioms R03SP01ThreeComponentZeroOneTwoSourceAssembly

/-- Reindex two exceptional triples as three A-positions, one B-position,
and two C-positions.  The intended exceptional paths are
A--A--B and A--C--C. -/
noncomputable def R03SP01ThreeComponentZeroOneTwoRearrange
    (a b c : Nat) :
    (((Fin a × Fin 3) ⊕
      ((Fin b × Fin 3) ⊕
        ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) ≃
      (((Fin a × Fin 3) ⊕ Fin 3) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕
          ((Fin c × Fin 3) ⊕ Fin 2))) := by
  let f :
      ((Fin a × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3)))) →
      (((Fin a × Fin 3) ⊕ Fin 3) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕
          ((Fin c × Fin 3) ⊕ Fin 2))) := fun x =>
    match x with
    | Sum.inl x => Sum.inl (Sum.inl x)
    | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (Sum.inl x))
    | Sum.inr (Sum.inr (Sum.inl x)) => Sum.inr (Sum.inr (Sum.inl x))
    | Sum.inr (Sum.inr (Sum.inr q)) =>
      if q.1 = 0 then
        if q.2 = 0 then Sum.inl (Sum.inr 0)
        else if q.2 = 1 then Sum.inl (Sum.inr 1)
        else Sum.inr (Sum.inl (Sum.inr 0))
      else if q.2 = 0 then Sum.inl (Sum.inr 2)
      else if q.2 = 1 then Sum.inr (Sum.inr (Sum.inr 0))
      else Sum.inr (Sum.inr (Sum.inr 1))
  let g :
      (((Fin a × Fin 3) ⊕ Fin 3) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕
          ((Fin c × Fin 3) ⊕ Fin 2))) →
      ((Fin a × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3)))) := fun x =>
    match x with
    | Sum.inl (Sum.inl x) => Sum.inl x
    | Sum.inl (Sum.inr s) =>
      if s = 0 then Sum.inr (Sum.inr (Sum.inr (0, 0)))
      else if s = 1 then Sum.inr (Sum.inr (Sum.inr (0, 1)))
      else Sum.inr (Sum.inr (Sum.inr (1, 0)))
    | Sum.inr (Sum.inl (Sum.inl x)) => Sum.inr (Sum.inl x)
    | Sum.inr (Sum.inl (Sum.inr _)) =>
      Sum.inr (Sum.inr (Sum.inr (0, 2)))
    | Sum.inr (Sum.inr (Sum.inl x)) =>
      Sum.inr (Sum.inr (Sum.inl x))
    | Sum.inr (Sum.inr (Sum.inr s)) =>
      if s = 0 then Sum.inr (Sum.inr (Sum.inr (1, 1)))
      else Sum.inr (Sum.inr (Sum.inr (1, 2)))
  have hleft : Function.LeftInverse g f := by
    intro x
    cases x with
    | inl x => simp [f, g]
    | inr x =>
      cases x with
      | inl x => simp [f, g]
      | inr x =>
        cases x with
        | inl x => simp [f, g]
        | inr q =>
          rcases q with ⟨i, j⟩
          fin_cases i <;> fin_cases j <;> simp [f, g]
  have hright : Function.RightInverse g f := by
    intro x
    cases x with
    | inl x =>
      cases x with
      | inl x => simp [f, g]
      | inr s => fin_cases s <;> simp [f, g]
    | inr x =>
      cases x with
      | inl x =>
        cases x with
        | inl x => simp [f, g]
        | inr s => fin_cases s <;> simp [f, g]
      | inr x =>
        cases x with
        | inl x => simp [f, g]
        | inr s => fin_cases s <;> simp [f, g]
  exact { toFun := f, invFun := g, left_inv := hleft, right_inv := hright }

#print axioms R03SP01ThreeComponentZeroOneTwoRearrange

/-- Put residual triples after the exceptional coordinates in each component
and compose the finite coordinate changes with the preceding rearrangement. -/
noncomputable def R03SP01ThreeComponentZeroOneTwoTargetMap
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat)
    (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C) :
    (((Fin a × Fin 3) ⊕
      ((Fin b × Fin 3) ⊕
        ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) ≃
      (A ⊕ (B ⊕ C)) := by
  let aIndex : ((Fin a × Fin 3) ⊕ Fin 3) ≃ Fin (3 + a * 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 3))).trans
      ((Equiv.sumComm (Fin (a * 3)) (Fin 3)).trans
        (finSumFinEquiv (m := 3) (n := a * 3)))
  let bIndex : ((Fin b × Fin 3) ⊕ Fin 1) ≃ Fin (1 + b * 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 1))).trans
      ((Equiv.sumComm (Fin (b * 3)) (Fin 1)).trans
        (finSumFinEquiv (m := 1) (n := b * 3)))
  let cIndex : ((Fin c × Fin 3) ⊕ Fin 2) ≃ Fin (2 + c * 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans
      ((Equiv.sumComm (Fin (c * 3)) (Fin 2)).trans
        (finSumFinEquiv (m := 2) (n := c * 3)))
  let components :
      (((Fin a × Fin 3) ⊕ Fin 3) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕
          ((Fin c × Fin 3) ⊕ Fin 2))) ≃ (A ⊕ (B ⊕ C)) :=
    Equiv.sumCongr (aIndex.trans eA)
      (Equiv.sumCongr (bIndex.trans eB) (cIndex.trans eC))
  exact (R03SP01ThreeComponentZeroOneTwoRearrange a b c).trans components

#print axioms R03SP01ThreeComponentZeroOneTwoTargetMap

/-- Target-map specialization of the mixed-residue source assembly.  This
form isolates the finite reindexing from the cyclic-order edge extraction. -/
theorem R03SP01ThreeComponentZeroOneTwoTargetAssembly
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (a b c : Nat)
    (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (hA : ∀ i : Fin a,
      G.Adj ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
        (Sum.inl (i, (0 : Fin 3))))
        ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
          (Sum.inl (i, (1 : Fin 3)))) ∧
      G.Adj ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
        (Sum.inl (i, (1 : Fin 3))))
        ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
          (Sum.inl (i, (2 : Fin 3)))))
    (hB : ∀ i : Fin b,
      G.Adj ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
        (Sum.inr (Sum.inl (i, (0 : Fin 3)))))
        ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
          (Sum.inr (Sum.inl (i, (1 : Fin 3))))) ∧
      G.Adj ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
        (Sum.inr (Sum.inl (i, (1 : Fin 3)))))
        ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
          (Sum.inr (Sum.inl (i, (2 : Fin 3))))))
    (hC : ∀ i : Fin c,
      G.Adj ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
        (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3))))))
        ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
          (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))) ∧
      G.Adj ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
        (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))
        ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
          (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3)))))))
    (hExc01 : ∀ i : Fin 2,
      G.Adj ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
        (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3))))))
        ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
          (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))))
    (hExc12 : ∀ i : Fin 2,
      G.Adj ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
        (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))
        ((R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
          (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3))))))) :
    Nonempty (P3Factor G) := by
  exact R03SP01ThreeComponentZeroOneTwoSourceAssembly G a b c
    (R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC)
    hA hB hC hExc01 hExc12

#print axioms R03SP01ThreeComponentZeroOneTwoTargetAssembly

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_A
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin a) (j : Fin 3) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inl (i, j)) =
      Sum.inl (eA ⟨3 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_B
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin b) (j : Fin 3) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inr (Sum.inl (i, j))) =
      Sum.inr (Sum.inl (eB ⟨1 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩)) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_C
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin c) (j : Fin 3) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inl (i, j)))) =
      Sum.inr (Sum.inr (eC ⟨2 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩)) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc00
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr ((0 : Fin 2), (0 : Fin 3))))) =
      Sum.inl (eA 0) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv] <;> try { apply Fin.ext; simp }

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc01
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr ((0 : Fin 2), (1 : Fin 3))))) =
      Sum.inl (eA 1) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv]
  apply Fin.ext
  norm_num [Fin.val_castAdd, Fin.val_ofNat,
    Nat.mod_eq_of_lt (by omega : 1 < 3 + a * 3)]

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc02
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr ((0 : Fin 2), (2 : Fin 3))))) =
      Sum.inr (Sum.inl (eB 0)) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv] <;> try { apply Fin.ext; simp }

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc10
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr ((1 : Fin 2), (0 : Fin 3))))) =
      Sum.inl (eA 2) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv]
  apply Fin.ext
  norm_num [Fin.val_castAdd, Fin.val_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 < 3 + a * 3)]

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc11
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr ((1 : Fin 2), (1 : Fin 3))))) =
      Sum.inr (Sum.inr (eC 0)) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv] <;> try { apply Fin.ext; simp }

theorem R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc12
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (a b c : Nat) (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B) (eC : Fin (2 + c * 3) ≃ C) :
    R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr ((1 : Fin 2), (2 : Fin 3))))) =
      Sum.inr (Sum.inr (eC 1)) := by
  simp [R03SP01ThreeComponentZeroOneTwoTargetMap,
    R03SP01ThreeComponentZeroOneTwoRearrange,
    Equiv.trans_apply, finProdFinEquiv]
  apply Fin.ext
  norm_num [Fin.val_castAdd, Fin.val_ofNat,
    Nat.mod_eq_of_lt (by omega : 1 < 2 + c * 3)]

/-- Fixed-coordinate cyclic specialization.  The first exceptional path is
A[0]--A[1]--B[0] and the second is A[2]--C[0]--C[1]; all residual triples
start immediately after the three A exceptional positions. -/
theorem R03SP01ThreeComponentZeroOneTwoCrossAssembly
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (a b c : Nat)
    (eA : Fin (3 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (cycleA : ∀ i : Fin (3 + a * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (3 + a * 3), Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (1 + b * 3),
      G.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨(i.val + 1) % (1 + b * 3),
          Nat.mod_lt _ (by omega)⟩))))
    (cycleC : ∀ i : Fin (2 + c * 3),
      G.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨(i.val + 1) % (2 + c * 3),
          Nat.mod_lt _ (by omega)⟩))))
    (crossAB : G.Adj (Sum.inl (eA 1))
      (Sum.inr (Sum.inl (eB 0))))
    (crossAC : G.Adj (Sum.inl (eA 2))
      (Sum.inr (Sum.inr (eC 0)))) :
    Nonempty (P3Factor G) := by
  let T := R03SP01ThreeComponentZeroOneTwoTargetMap a b c eA eB eC
  have hA : ∀ i : Fin a,
      G.Adj (T (Sum.inl (i, (0 : Fin 3))))
        (T (Sum.inl (i, (1 : Fin 3)))) ∧
      G.Adj (T (Sum.inl (i, (1 : Fin 3))))
        (T (Sum.inl (i, (2 : Fin 3)))) := by
    intro i
    constructor
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_A
        a b c eA eB eC i 0,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_A
          a b c eA eB eC i 1]
      have h := cycleA ⟨3 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext :
          eA (⟨(3 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1) %
              (3 + a * 3), Nat.mod_lt _ (by omega)⟩ : Fin (3 + a * 3)) =
            eA ⟨3 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
              simp [finProdFinEquiv]
              omega⟩ := by
        apply congrArg eA
        apply Fin.ext
        have hlt : 3 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1 <
            3 + a * 3 := by
          simp [finProdFinEquiv]
          omega
        change (3 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1) %
          (3 + a * 3) = 3 + (finProdFinEquiv (i, (1 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      simpa only [hnext] using h
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_A
        a b c eA eB eC i 1,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_A
          a b c eA eB eC i 2]
      have h := cycleA ⟨3 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext :
          eA (⟨(3 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1) %
              (3 + a * 3), Nat.mod_lt _ (by omega)⟩ : Fin (3 + a * 3)) =
            eA ⟨3 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
              simp [finProdFinEquiv]
              omega⟩ := by
        apply congrArg eA
        apply Fin.ext
        have hlt : 3 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1 <
            3 + a * 3 := by
          simp [finProdFinEquiv]
          omega
        change (3 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1) %
          (3 + a * 3) = 3 + (finProdFinEquiv (i, (2 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      simpa only [hnext] using h
  have hB : ∀ i : Fin b,
      G.Adj (T (Sum.inr (Sum.inl (i, (0 : Fin 3)))))
        (T (Sum.inr (Sum.inl (i, (1 : Fin 3))))) ∧
      G.Adj (T (Sum.inr (Sum.inl (i, (1 : Fin 3)))))
        (T (Sum.inr (Sum.inl (i, (2 : Fin 3))))) := by
    intro i
    constructor
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_B
        a b c eA eB eC i 0,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_B
          a b c eA eB eC i 1]
      have h := cycleB ⟨1 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext :
          eB (⟨(1 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1) %
              (1 + b * 3), Nat.mod_lt _ (by omega)⟩ : Fin (1 + b * 3)) =
            eB ⟨1 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
              simp [finProdFinEquiv]
              omega⟩ := by
        apply congrArg eB
        apply Fin.ext
        have hlt : 1 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1 <
            1 + b * 3 := by
          simp [finProdFinEquiv]
          omega
        change (1 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1) %
          (1 + b * 3) = 1 + (finProdFinEquiv (i, (1 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      simpa only [hnext] using h
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_B
        a b c eA eB eC i 1,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_B
          a b c eA eB eC i 2]
      have h := cycleB ⟨1 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext :
          eB (⟨(1 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1) %
              (1 + b * 3), Nat.mod_lt _ (by omega)⟩ : Fin (1 + b * 3)) =
            eB ⟨1 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
              simp [finProdFinEquiv]
              omega⟩ := by
        apply congrArg eB
        apply Fin.ext
        have hlt : 1 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1 <
            1 + b * 3 := by
          simp [finProdFinEquiv]
          omega
        change (1 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1) %
          (1 + b * 3) = 1 + (finProdFinEquiv (i, (2 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      simpa only [hnext] using h
  have hC : ∀ i : Fin c,
      G.Adj (T (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3))))))
        (T (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))) ∧
      G.Adj (T (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))
        (T (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3)))))) := by
    intro i
    constructor
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_C
        a b c eA eB eC i 0,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_C
          a b c eA eB eC i 1]
      have h := cycleC ⟨2 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext :
          eC (⟨(2 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1) %
              (2 + c * 3), Nat.mod_lt _ (by omega)⟩ : Fin (2 + c * 3)) =
            eC ⟨2 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
              simp [finProdFinEquiv]
              omega⟩ := by
        apply congrArg eC
        apply Fin.ext
        have hlt : 2 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1 <
            2 + c * 3 := by
          simp [finProdFinEquiv]
          omega
        change (2 + (finProdFinEquiv (i, (0 : Fin 3))).val + 1) %
          (2 + c * 3) = 2 + (finProdFinEquiv (i, (1 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      simpa only [hnext] using h
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_C
        a b c eA eB eC i 1,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_C
          a b c eA eB eC i 2]
      have h := cycleC ⟨2 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext :
          eC (⟨(2 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1) %
              (2 + c * 3), Nat.mod_lt _ (by omega)⟩ : Fin (2 + c * 3)) =
            eC ⟨2 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
              simp [finProdFinEquiv]
              omega⟩ := by
        apply congrArg eC
        apply Fin.ext
        have hlt : 2 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1 <
            2 + c * 3 := by
          simp [finProdFinEquiv]
          omega
        change (2 + (finProdFinEquiv (i, (1 : Fin 3))).val + 1) %
          (2 + c * 3) = 2 + (finProdFinEquiv (i, (2 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      simpa only [hnext] using h
  have hExc01 : ∀ i : Fin 2,
      G.Adj (T (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3))))))
        (T (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))) := by
    intro i
    fin_cases i
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc00
          a b c eA eB eC,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc01
          a b c eA eB eC]
      exact cycleA 0
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc10
          a b c eA eB eC,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc11
          a b c eA eB eC]
      exact crossAC
  have hExc12 : ∀ i : Fin 2,
      G.Adj (T (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))
        (T (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3)))))) := by
    intro i
    fin_cases i
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc01
          a b c eA eB eC,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc02
          a b c eA eB eC]
      exact crossAB
    · dsimp [T]
      rw [R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc11
          a b c eA eB eC,
        R03SP01ThreeComponentZeroOneTwoTargetMap_apply_exc12
          a b c eA eB eC]
      exact cycleC 0
  exact R03SP01ThreeComponentZeroOneTwoTargetAssembly G a b c eA eB eC
    hA hB hC hExc01 hExc12

#print axioms R03SP01ThreeComponentZeroOneTwoCrossAssembly

/-- Ambient two-factor transport for the mixed 0/1/2 component profile.  The
cyclic orders and the two cross edges are still supplied data; this wrapper
only transports them through a support equivalence and the subgraph relation
of a TwoFactor. -/
theorem R03SP01ThreeComponentZeroOneTwoCrossAssemblyOfTwoFactor
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB cC : F.ConnectedComponent)
    (eV : cA.supp ⊕ (cB.supp ⊕ cC.supp) ≃ V)
    (heA : ∀ x : cA.supp, eV (Sum.inl x) = x.1)
    (heB : ∀ x : cB.supp, eV (Sum.inr (Sum.inl x)) = x.1)
    (heC : ∀ x : cC.supp, eV (Sum.inr (Sum.inr x)) = x.1)
    (a b c : Nat)
    [Fintype cA.supp] [Fintype cB.supp] [Fintype cC.supp]
    (eA : Fin (3 + a * 3) ≃ cA.supp)
    (eB : Fin (1 + b * 3) ≃ cB.supp)
    (eC : Fin (2 + c * 3) ≃ cC.supp)
    (cycleA : ∀ i : Fin (3 + a * 3),
      F.Adj (eA i)
        (eA ⟨(i.val + 1) % (3 + a * 3), Nat.mod_lt _ (by omega)⟩))
    (cycleB : ∀ i : Fin (1 + b * 3),
      F.Adj (eB i)
        (eB ⟨(i.val + 1) % (1 + b * 3), Nat.mod_lt _ (by omega)⟩))
    (cycleC : ∀ i : Fin (2 + c * 3),
      F.Adj (eC i)
        (eC ⟨(i.val + 1) % (2 + c * 3), Nat.mod_lt _ (by omega)⟩))
    (crossAB : G.Adj (eV (Sum.inl (eA 1)))
      (eV (Sum.inr (Sum.inl (eB 0)))))
    (crossAC : G.Adj (eV (Sum.inl (eA 2)))
      (eV (Sum.inr (Sum.inr (eC 0))))) :
    Nonempty (P3Factor G) := by
  classical
  let Gsum : SimpleGraph (cA.supp ⊕ (cB.supp ⊕ cC.supp)) := G.comap eV
  have hA : ∀ i : Fin (3 + a * 3),
      Gsum.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (3 + a * 3), Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    simpa [Gsum, heA] using hTF.1 (cycleA i)
  have hB : ∀ i : Fin (1 + b * 3),
      Gsum.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨(i.val + 1) % (1 + b * 3), Nat.mod_lt _ (by omega)⟩))) := by
    intro i
    simpa [Gsum, heB] using hTF.1 (cycleB i)
  have hC : ∀ i : Fin (2 + c * 3),
      Gsum.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨(i.val + 1) % (2 + c * 3), Nat.mod_lt _ (by omega)⟩))) := by
    intro i
    simpa [Gsum, heC] using hTF.1 (cycleC i)
  have hAB : Gsum.Adj (Sum.inl (eA 1))
      (Sum.inr (Sum.inl (eB 0))) := by
    change G.Adj (eV (Sum.inl (eA 1)))
      (eV (Sum.inr (Sum.inl (eB 0))))
    exact crossAB
  have hAC : Gsum.Adj (Sum.inl (eA 2))
      (Sum.inr (Sum.inr (eC 0))) := by
    change G.Adj (eV (Sum.inl (eA 2)))
      (eV (Sum.inr (Sum.inr (eC 0))))
    exact crossAC
  obtain ⟨p⟩ := R03SP01ThreeComponentZeroOneTwoCrossAssembly
    Gsum a b c eA eB eC hA hB hC hAB hAC
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans eV
    edge01 := ?_
    edge12 := ?_ }⟩
  · intro i
    exact p.edge01 i
  · intro i
    exact p.edge12 i

#print axioms R03SP01ThreeComponentZeroOneTwoCrossAssemblyOfTwoFactor


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (hcycles : F.IsCycles)
    (h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2)
    (c : F.ConnectedComponent) (n : Nat) [Fintype c.supp]
    (hn : 0 < n)
    (hcard : Fintype.card c.supp = n) :
    ∃ e : Fin n ≃ c.supp, ∀ i : Fin n,
      F.Adj (e i : V)
        (e ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : V) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨v, hv⟩ := c.nonempty_supp
  have hvne : (F.neighborSet v).Nonempty := by
    have hcardv : (F.neighborSet v).ncard = 2 := by
      change Nat.card {w : V // F.Adj v w} = 2
      exact h2 v
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨p, hp, hpverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hvne
  have hpne : ¬ p.Nil := hp.not_nil
  let q := p.tail
  have hqnodup : q.support.Nodup := by
    rw [show q.support = p.support.tail by
      dsimp [q]
      exact p.support_tail_of_not_nil hpne]
    exact hp.support_nodup
  have hqset : {x : V | x ∈ q.support} = c.supp := by
    ext x
    constructor
    · intro hx
      have hxps : x ∈ p.support := by
        rw [p.mem_support_iff]
        right
        have hxq : x ∈ p.tail.support := by
          change x ∈ q.support at hx
          exact hx
        rw [p.support_tail_of_not_nil hpne] at hxq
        exact hxq
      rw [← hpverts]
      exact (p.mem_verts_toSubgraph).2 hxps
    · intro hx
      have hxverts : x ∈ p.toSubgraph.verts := hpverts ▸ hx
      have hxps : x ∈ p.support := (p.mem_verts_toSubgraph).1 hxverts
      rw [p.mem_support_iff] at hxps
      rcases hxps with rfl | hxt
      · change x ∈ p.tail.support
        rw [p.support_tail_of_not_nil hpne]
        exact p.end_mem_tail_support hpne
      · change x ∈ p.tail.support
        rw [p.support_tail_of_not_nil hpne]
        exact hxt
  let eList : Fin q.support.length ≃ {x : V // x ∈ q.support} :=
    List.Nodup.getEquiv q.support hqnodup
  let eSet : {x : V // x ∈ q.support} ≃ c.supp := Equiv.setCongr hqset
  have hlen : q.support.length = n := by
    calc
      q.support.length = Fintype.card {x : V // x ∈ q.support} := by
        symm
        simpa using (Fintype.card_congr eList).symm
      _ = Fintype.card c.supp := Fintype.card_congr eSet
      _ = n := hcard
  let e : Fin n ≃ c.supp :=
    (finCongr hlen.symm).trans (eList.trans eSet)
  refine ⟨e, ?_⟩
  intro i
  have he (j : Fin n) : (e j : V) = q.getVert (j : Nat) := by
    dsimp [e, eSet, eList]
    change q.support.get (finCongr hlen.symm j) = _
    rw [← q.getVert_comp_val_eq_get_support]
    rfl
  rw [he i]
  by_cases hi : (i : Nat) < q.length
  · have hadj := q.adj_getVert_succ hi
    have hin : i.val + 1 < n := by
      have hi' : i.val < q.support.length := by rw [hlen]; exact i.isLt
      have hlenq : q.length + 1 = n := q.length_support.symm.trans hlen
      rw [q.length_support] at hi'
      omega
    have hnext : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) =
        ⟨i.val + 1, by omega⟩ := by
      ext
      exact Nat.mod_eq_of_lt hin
    rw [hnext, he]
    exact hadj
  · have hilast : (i : Nat) = q.length := by
      have hqplus : q.support.length = q.length + 1 := q.length_support
      have hilt : (i : Nat) < q.support.length := by rw [hlen]; exact i.isLt
      omega
    have hqend : q.getVert q.length = p.getVert p.length := by
      simp only [q, SimpleGraph.Walk.getVert_tail]
      rw [p.length_tail_add_one hpne]
    have hqstart : q.getVert 0 = p.snd := by
      simp [q]
    have hadj : F.Adj (q.getVert q.length) (q.getVert 0) := by
      rw [hqend, hqstart, p.getVert_length]
      exact p.adj_snd hpne
    have hnlen : n = q.length + 1 := by
      calc
        n = q.support.length := hlen.symm
        _ = q.length + 1 := q.length_support
    have hnext : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      rw [hilast]
      apply Nat.mod_eq_zero_of_dvd
      rw [hnlen]
    have hfirst : q.getVert (i : Nat) = q.getVert q.length := by
      rw [hilast]
    rw [hfirst, hnext, he]
    exact hadj

