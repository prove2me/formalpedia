-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneArbitraryPortsTargetMod0
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:21:57.667026+00:00
-- url     : https://prove2.me/submissions/dd57f44b-e482-41a3-8d46-0c19520fc8aa

import Mathlib

namespace CubicP3Partition

set_option maxRecDepth 100000

/-- Reindex the five local pieces of the d ≡ 0 arbitrary-port construction.
The source keeps the two exceptional triples together; the target moves their
six positions into the A-, B-, and C-component sources.  This is a pure finite
bijection, independent of any graph edges. -/
theorem R03SP01ThreeOneArbitraryPortsRearrangeMod0
    (a k1 k2 c : Nat) :
    Nonempty
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
          if q.2 = 0 then Sum.inl (Sum.inr 0)
          else if q.2 = 1 then
            Sum.inr (Sum.inr (Sum.inr (Sum.inl 0)))
          else
            Sum.inr (Sum.inr (Sum.inr (Sum.inl 1)))
        else if q.2 = 0 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inl 2)))
        else if q.2 = 1 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inl 3)))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr 0))))
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
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 0))))
    | Sum.inr (Sum.inl b1) => Sum.inr (Sum.inl b1)
    | Sum.inr (Sum.inr (Sum.inl b2)) =>
        Sum.inr (Sum.inr (Sum.inl b2))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl q))) =>
        if q = 0 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 1))))
        else if q = 1 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 2))))
        else if q = 2 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 0))))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 1))))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl c0)))) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inl c0)))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 2))))
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
  exact ⟨{ toFun := f, invFun := g, left_inv := hleft, right_inv := hright }⟩

#print axioms R03SP01ThreeOneArbitraryPortsRearrangeMod0



end CubicP3Partition

open CubicP3Partition
theorem solution
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    Nonempty
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
  obtain ⟨reindex⟩ := R03SP01ThreeOneArbitraryPortsRearrangeMod0 a k1 k2 c
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
  exact ⟨reindex.trans (grouped.trans components)⟩

