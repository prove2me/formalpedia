-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneArbitraryPortsAssemblyMod1ComponentEdges
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:21:38.661773+00:00
-- url     : https://prove2.me/submissions/6732da0f-c44f-49c5-a88f-d07ceef7ed5f

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

set_option maxRecDepth 100000

/-- Reindex the five local pieces of the d ≡ 1 arbitrary-port construction.
The source keeps the two exceptional triples together; the target moves their
six positions into the A-, B-, and C-component sources.  This is a pure finite
bijection, independent of any graph edges. -/
noncomputable def R03SP01ThreeOneArbitraryPortsRearrangeMapMod1
    (a k1 k2 c : Nat) :
    (((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) ≃
        (((Fin a × Fin 3) ⊕ Fin 1) ⊕
          ((Fin k1 × Fin 3) ⊕
            ((Fin k2 × Fin 3) ⊕
              (Fin 4 ⊕ ((Fin c × Fin 3) ⊕ Fin 1)))))) := by
  let f :
      ((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) →
      ((Fin a × Fin 3) ⊕ Fin 1) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            (Fin 4 ⊕ ((Fin c × Fin 3) ⊕ Fin 1)))) := fun x =>
    match x with
    | Sum.inl a0 => Sum.inl (Sum.inl a0)
    | Sum.inr (Sum.inl b1) =>
        Sum.inr (Sum.inl b1)
    | Sum.inr (Sum.inr (Sum.inl b2)) =>
        Sum.inr (Sum.inr (Sum.inl b2))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl c0))) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c0))))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) =>
        if q.1 = 0 then
          if q.2 = 0 then
            Sum.inr (Sum.inr (Sum.inr (Sum.inl 3)))
          else if q.2 = 1 then
            Sum.inr (Sum.inr (Sum.inr (Sum.inl 0)))
          else
            Sum.inl (Sum.inr 0)
        else if q.2 = 0 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr 0))))
        else if q.2 = 1 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inl 1)))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inl 2)))
  let g :
      ((Fin a × Fin 3) ⊕ Fin 1) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            (Fin 4 ⊕ ((Fin c × Fin 3) ⊕ Fin 1)))) →
      ((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) := fun x =>
    match x with
    | Sum.inl (Sum.inl a0) => Sum.inl a0
    | Sum.inl (Sum.inr _) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 2))))
    | Sum.inr (Sum.inl b1) => Sum.inr (Sum.inl b1)
    | Sum.inr (Sum.inr (Sum.inl b2)) =>
        Sum.inr (Sum.inr (Sum.inl b2))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl q))) =>
        if q = 0 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 1))))
        else if q = 1 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 1))))
        else if q = 2 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 2))))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 0))))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c0)))) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inl c0)))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 0))))
  have hleft : Function.LeftInverse g f := by
    intro x
    cases x with
    | inl a0 =>
      simp [f, g]
    | inr x =>
      cases x with
      | inl b1 =>
        simp [f, g]
      | inr x =>
        cases x with
        | inl b2 =>
          simp [f, g]
        | inr x =>
          cases x with
          | inl c0 =>
            simp [f, g]
          | inr q =>
            rcases q with ⟨i, j⟩
            fin_cases i <;> fin_cases j <;> simp [f, g]
  have hright : Function.RightInverse g f := by
    intro x
    cases x with
    | inl x =>
      cases x with
      | inl a0 =>
        simp [f, g]
      | inr one =>
        have hone : one = 0 := Subsingleton.elim _ _
        subst one
        simp [f, g]
    | inr x =>
      cases x with
      | inl b1 =>
        simp [f, g]
      | inr x =>
        cases x with
        | inl b2 =>
          simp [f, g]
        | inr x =>
          cases x with
          | inl q =>
            fin_cases q <;> simp [f, g]
          | inr x =>
            cases x with
            | inl c0 =>
              simp [f, g]
            | inr one =>
              have hone : one = 0 := Subsingleton.elim _ _
              subst one
              simp [f, g]
  exact { toFun := f, invFun := g, left_inv := hleft, right_inv := hright }

#print axioms R03SP01ThreeOneArbitraryPortsRearrangeMapMod1


noncomputable def R03SP01ThreeOneArbitraryPortsTargetMapMod1
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    (((Fin a × Fin 3) ⊕
      ((Fin k1 × Fin 3) ⊕
        ((Fin k2 × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) ≃
      (A ⊕ (B ⊕ C))) := by
  let shiftA : (Fin (a * 3) ⊕ Fin 1) ≃ Fin (1 + a * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1))
  let aProd : ((Fin a × Fin 3) ⊕ Fin 1) ≃
      (Fin (a * 3) ⊕ Fin 1) :=
    Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 1))
  let aPart : ((Fin a × Fin 3) ⊕ Fin 1) ≃ A :=
    (aProd.trans shiftA).trans eA
  let bProd : ((Fin k1 × Fin 3) ⊕
      ((Fin k2 × Fin 3) ⊕ Fin 4)) ≃
      (Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4)) :=
    Equiv.sumCongr finProdFinEquiv
      (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 4)))
  let bPart : ((Fin k1 × Fin 3) ⊕
      ((Fin k2 × Fin 3) ⊕ Fin 4)) ≃ B :=
    (bProd.trans eIndex).trans eB
  let shiftC : (Fin (c * 3) ⊕ Fin 1) ≃ Fin (1 + c * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := c * 3) (n := 1))
  let cProd : ((Fin c × Fin 3) ⊕ Fin 1) ≃
      (Fin (c * 3) ⊕ Fin 1) :=
    Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 1))
  let cPart : ((Fin c × Fin 3) ⊕ Fin 1) ≃ C :=
    (cProd.trans shiftC).trans eC
  let reindex := R03SP01ThreeOneArbitraryPortsRearrangeMapMod1 a k1 k2 c
  let bAssoc :
      ((Fin k1 × Fin 3) ⊕
        ((Fin k2 × Fin 3) ⊕
          (Fin 4 ⊕ ((Fin c × Fin 3) ⊕ Fin 1)))) ≃
      (((Fin k1 × Fin 3) ⊕
        ((Fin k2 × Fin 3) ⊕ Fin 4)) ⊕
          ((Fin c × Fin 3) ⊕ Fin 1)) :=
    (Equiv.sumAssoc (Fin k1 × Fin 3) (Fin k2 × Fin 3)
      (Fin 4 ⊕ ((Fin c × Fin 3) ⊕ Fin 1))).symm.trans
      ((Equiv.sumAssoc ((Fin k1 × Fin 3) ⊕ (Fin k2 × Fin 3))
        (Fin 4) ((Fin c × Fin 3) ⊕ Fin 1)).symm.trans
        (Equiv.sumCongr
          (Equiv.sumAssoc (Fin k1 × Fin 3) (Fin k2 × Fin 3) (Fin 4))
          (Equiv.refl ((Fin c × Fin 3) ⊕ Fin 1))))
  let grouped :
      (((Fin a × Fin 3) ⊕ Fin 1) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            (Fin 4 ⊕ ((Fin c × Fin 3) ⊕ Fin 1))))) ≃
      (((Fin a × Fin 3) ⊕ Fin 1) ⊕
        ((((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕ Fin 4)) ⊕
            ((Fin c × Fin 3) ⊕ Fin 1)))) :=
    Equiv.sumCongr (Equiv.refl ((Fin a × Fin 3) ⊕ Fin 1)) bAssoc
  let components :
      (((Fin a × Fin 3) ⊕ Fin 1) ⊕
        ((((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕ Fin 4)) ⊕
            ((Fin c × Fin 3) ⊕ Fin 1)))) ≃
      (A ⊕ (B ⊕ C)) :=
    Equiv.sumCongr aPart (Equiv.sumCongr bPart cPart)
  exact reindex.trans (grouped.trans components)

#print axioms R03SP01ThreeOneArbitraryPortsTargetMapMod1


theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_A
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) (i : Fin a) (j : Fin 3) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inl (i, j)) =
      Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
        (Sum.inl (finProdFinEquiv (i, j))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1,
    R03SP01ThreeOneArbitraryPortsRearrangeMapMod1,
    Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_B1
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) (i : Fin k1) (j : Fin 3) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inl (i, j))) =
      Sum.inr (Sum.inl
        (eB (eIndex (Sum.inl (finProdFinEquiv (i, j)))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1,
    R03SP01ThreeOneArbitraryPortsRearrangeMapMod1,
    Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_B2
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) (i : Fin k2) (j : Fin 3) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inr (Sum.inl (i, j)))) =
      Sum.inr (Sum.inl
        (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv (i, j))))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1,
    R03SP01ThreeOneArbitraryPortsRearrangeMapMod1,
    Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_C
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) (i : Fin c) (j : Fin 3) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))) =
      Sum.inr (Sum.inr
        (eC ((finSumFinEquiv.trans (finAddFlip (m := c * 3) (n := 1)))
          (Sum.inl (finProdFinEquiv (i, j)))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1,
    R03SP01ThreeOneArbitraryPortsRearrangeMapMod1,
    Equiv.trans_apply, finProdFinEquiv]


theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excA
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((0 : Fin 2), (2 : Fin 3)))))) =
      Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1))) (Sum.inr (0 : Fin 1)))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1, R03SP01ThreeOneArbitraryPortsRearrangeMapMod1, Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB0
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((0 : Fin 2), (1 : Fin 3)))))) =
      (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (0 : Fin 4))))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1, R03SP01ThreeOneArbitraryPortsRearrangeMapMod1, Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB1
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((1 : Fin 2), (1 : Fin 3)))))) =
      (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (1 : Fin 4))))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1, R03SP01ThreeOneArbitraryPortsRearrangeMapMod1, Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB2
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((1 : Fin 2), (2 : Fin 3)))))) =
      (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (2 : Fin 4))))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1, R03SP01ThreeOneArbitraryPortsRearrangeMapMod1, Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB3
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((0 : Fin 2), (0 : Fin 3)))))) =
      (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (3 : Fin 4))))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1, R03SP01ThreeOneArbitraryPortsRearrangeMapMod1, Equiv.trans_apply, finProdFinEquiv]

theorem R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excC
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((1 : Fin 2), (0 : Fin 3)))))) =
      Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans (finAddFlip (m := c * 3) (n := 1))) (Sum.inr (0 : Fin 1))))) := by
  simp [R03SP01ThreeOneArbitraryPortsTargetMapMod1, R03SP01ThreeOneArbitraryPortsRearrangeMapMod1, Equiv.trans_apply, finProdFinEquiv]

#print axioms R03SP01ThreeOneArbitraryPortsTargetMapMod1



/-- Assemble five local families of ordered triples after an explicit target
bijection has identified their disjoint carriers with the ambient graph.  The
hypotheses are deliberately edge-local: four residual families and two
exceptional triples are checked directly in the target coordinates. -/
theorem R03SP01FivePieceSourceAssembly
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (a k1 k2 c : Nat)
    (target :
      (((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) ≃
        (A ⊕ (B ⊕ C))))
    (hA : ∀ i : Fin a,
      G.Adj (target (Sum.inl (i, (0 : Fin 3))))
        (target (Sum.inl (i, (1 : Fin 3)))) ∧
      G.Adj (target (Sum.inl (i, (1 : Fin 3))))
        (target (Sum.inl (i, (2 : Fin 3)))))
    (hB1 : ∀ i : Fin k1,
      G.Adj (target (Sum.inr (Sum.inl (i, (0 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (1 : Fin 3))))) ∧
      G.Adj (target (Sum.inr (Sum.inl (i, (1 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (2 : Fin 3))))))
    (hB2 : ∀ i : Fin k2,
      G.Adj (target (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3))))))
        (target (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))) ∧
      G.Adj (target (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))
        (target (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3)))))))
    (hC : ∀ i : Fin c,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))) ∧
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3))))))))
    (hExc01 : ∀ i : Fin 2,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))))
    (hExc12 : ∀ i : Fin 2,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3)))))))) :
    Nonempty (P3Factor G) := by
  let rest1 := k1 + (k2 + (c + 2))
  let rest2 := k2 + (c + 2)
  let rest3 := c + 2
  let blockSum : Fin (a + (k1 + (k2 + (c + 2)))) ≃
      Fin a ⊕ (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 2))) :=
    finSumFinEquiv.symm.trans
      (Equiv.sumCongr (Equiv.refl (Fin a))
        (finSumFinEquiv.symm.trans
          (Equiv.sumCongr (Equiv.refl (Fin k1))
            (finSumFinEquiv.symm.trans
              (Equiv.sumCongr (Equiv.refl (Fin k2))
                finSumFinEquiv.symm)))))
  let dA : (Fin a ⊕ (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 2))) ) × Fin 3 ≃
      (Fin a × Fin 3) ⊕
        ((Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 2))) × Fin 3) :=
    Equiv.sumProdDistrib (Fin a)
      (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 2))) (Fin 3)
  let dB : (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 2))) × Fin 3 ≃
      (Fin k1 × Fin 3) ⊕
        ((Fin k2 ⊕ (Fin c ⊕ Fin 2)) × Fin 3) :=
    Equiv.sumProdDistrib (Fin k1) (Fin k2 ⊕ (Fin c ⊕ Fin 2)) (Fin 3)
  let dC : (Fin k2 ⊕ (Fin c ⊕ Fin 2)) × Fin 3 ≃
      (Fin k2 × Fin 3) ⊕ ((Fin c ⊕ Fin 2) × Fin 3) :=
    Equiv.sumProdDistrib (Fin k2) (Fin c ⊕ Fin 2) (Fin 3)
  let dD : (Fin c ⊕ Fin 2) × Fin 3 ≃
      (Fin c × Fin 3) ⊕ (Fin 2 × Fin 3) :=
    Equiv.sumProdDistrib (Fin c) (Fin 2) (Fin 3)
  let distributed :
      (Fin a ⊕ (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 2)))) × Fin 3 ≃
      ((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) :=
    dA.trans (Equiv.sumCongr (Equiv.refl (Fin a × Fin 3))
      (dB.trans (Equiv.sumCongr (Equiv.refl (Fin k1 × Fin 3))
        (dC.trans (Equiv.sumCongr (Equiv.refl (Fin k2 × Fin 3)) dD)))))
  let blockToSource :
      (Fin (a + (k1 + (k2 + (c + 2)))) × Fin 3) ≃
      ((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) :=
    (blockSum.prodCongr (Equiv.refl (Fin 3))).trans distributed
  let place : (Fin (a + (k1 + (k2 + (c + 2)))) × Fin 3) ≃
      (A ⊕ (B ⊕ C)) := blockToSource.trans target
  refine ⟨{
    blockCount := a + (k1 + (k2 + (c + 2)))
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have h := (hA i).1
      simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
        Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
        finProdFinEquiv] using h
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have h := (hB1 i).1
        simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
          Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
          finProdFinEquiv] using h
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · have h := (hB2 i).1
          simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
            Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
            finProdFinEquiv] using h
        · refine Fin.addCases (m := c) (n := 2) (fun j => ?_) (fun j => ?_) i
          · have h := (hC j).1
            simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
              Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
              finProdFinEquiv] using h
          · fin_cases j
            · have h := hExc01 0
              simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
                Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
                finProdFinEquiv] using h
            · have h := hExc01 1
              simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
                Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
                finProdFinEquiv] using h
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have h := (hA i).2
      simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
        Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
        finProdFinEquiv] using h
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have h := (hB1 i).2
        simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
          Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
          finProdFinEquiv] using h
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · have h := (hB2 i).2
          simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
            Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
            finProdFinEquiv] using h
        · refine Fin.addCases (m := c) (n := 2) (fun j => ?_) (fun j => ?_) i
          · have h := (hC j).2
            simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
              Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
              finProdFinEquiv] using h
          · fin_cases j
            · have h := hExc12 0
              simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
                Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
                finProdFinEquiv] using h
            · have h := hExc12 1
              simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
                Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
                finProdFinEquiv] using h

#print axioms R03SP01FivePieceSourceAssembly



end CubicP3Partition

open CubicP3Partition
theorem solution
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3))
    (hAraw : ∀ i : Fin a,
      G.Adj
          (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (0 : Fin 3)))))))
          (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (1 : Fin 3))))))) ∧
      G.Adj
          (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (1 : Fin 3)))))))
          (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (2 : Fin 3))))))))
    (hB1raw : ∀ i : Fin k1,
      G.Adj
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inl (finProdFinEquiv
            (i, (0 : Fin 3))))))))
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inl (finProdFinEquiv
            (i, (1 : Fin 3)))))))) ∧
      G.Adj
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inl (finProdFinEquiv
            (i, (1 : Fin 3))))))))
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inl (finProdFinEquiv
            (i, (2 : Fin 3)))))))))
    (hB2raw : ∀ i : Fin k2,
      G.Adj
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv
            (i, (0 : Fin 3)))))))))
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv
            (i, (1 : Fin 3))))))))) ∧
      G.Adj
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv
            (i, (1 : Fin 3)))))))))
          (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inl (finProdFinEquiv
            (i, (2 : Fin 3))))))))))
    (hCraw : ∀ i : Fin c,
      G.Adj
          (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans
            (finAddFlip (m := c * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (0 : Fin 3))))))))
          (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans
            (finAddFlip (m := c * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (1 : Fin 3)))))))) ∧
      G.Adj
          (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans
            (finAddFlip (m := c * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (1 : Fin 3))))))))
          (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans
            (finAddFlip (m := c * 3) (n := 1)))
            (Sum.inl (finProdFinEquiv (i, (2 : Fin 3)))))))))
    (hAB : G.Adj (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (3 : Fin 4))))))) (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (0 : Fin 4))))))))
    (hB01 : G.Adj (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (0 : Fin 4))))))) (Sum.inl (eA ((finSumFinEquiv.trans (finAddFlip (m := a * 3) (n := 1))) (Sum.inr (0 : Fin 1))))))
    (hB23 : G.Adj (Sum.inr (Sum.inr (eC ((finSumFinEquiv.trans (finAddFlip (m := c * 3) (n := 1))) (Sum.inr (0 : Fin 1)))))) (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (1 : Fin 4))))))))
    (hBC : G.Adj (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (1 : Fin 4))))))) (Sum.inr (Sum.inl (eB (eIndex (Sum.inr (Sum.inr (2 : Fin 4)))))))) :
    Nonempty (P3Factor G) := by
  let T := R03SP01ThreeOneArbitraryPortsTargetMapMod1 a b c k1 k2 eA eB eC eIndex
  have hA : ∀ i : Fin a,
      G.Adj (T (Sum.inl (i, (0 : Fin 3))))
        (T (Sum.inl (i, (1 : Fin 3)))) ∧
      G.Adj (T (Sum.inl (i, (1 : Fin 3))))
        (T (Sum.inl (i, (2 : Fin 3)))) := by
    intro i
    have h := hAraw i
    simpa only [T, R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_A] using h
  have hB1 : ∀ i : Fin k1,
      G.Adj (T (Sum.inr (Sum.inl (i, (0 : Fin 3)))))
        (T (Sum.inr (Sum.inl (i, (1 : Fin 3))))) ∧
      G.Adj (T (Sum.inr (Sum.inl (i, (1 : Fin 3)))))
        (T (Sum.inr (Sum.inl (i, (2 : Fin 3))))) := by
    intro i
    have h := hB1raw i
    simpa only [T, R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_B1] using h
  have hB2 : ∀ i : Fin k2,
      G.Adj (T (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3))))))
        (T (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))) ∧
      G.Adj (T (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))
        (T (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3)))))) := by
    intro i
    have h := hB2raw i
    simpa only [T, R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_B2] using h
  have hC : ∀ i : Fin c,
      G.Adj (T (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3)))))))
        (T (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))) ∧
      G.Adj (T (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))))
        (T (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3))))))) := by
    intro i
    have h := hCraw i
    simpa only [T, R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_C] using h
  have hExc01 : ∀ i : Fin 2,
      G.Adj (T (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3)))))))
        (T (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))) := by
    intro i
    fin_cases i
    · dsimp [T]
      rw [R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB3 a b c k1 k2 eA eB eC eIndex,
        R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB0 a b c k1 k2 eA eB eC eIndex]
      exact hAB
    · dsimp [T]
      rw [R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excC a b c k1 k2 eA eB eC eIndex,
        R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB1 a b c k1 k2 eA eB eC eIndex]
      exact hB23
  have hExc12 : ∀ i : Fin 2,
      G.Adj (T (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))))
        (T (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3))))))) := by
    intro i
    fin_cases i
    · dsimp [T]
      rw [R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB0 a b c k1 k2 eA eB eC eIndex,
        R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excA a b c k1 k2 eA eB eC eIndex]
      exact hB01
    · dsimp [T]
      rw [R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB1 a b c k1 k2 eA eB eC eIndex,
        R03SP01ThreeOneArbitraryPortsTargetMapMod1_apply_excB2 a b c k1 k2 eA eB eC eIndex]
      exact hBC
  exact R03SP01FivePieceSourceAssembly G a k1 k2 c T hA hB1 hB2 hC hExc01 hExc12

