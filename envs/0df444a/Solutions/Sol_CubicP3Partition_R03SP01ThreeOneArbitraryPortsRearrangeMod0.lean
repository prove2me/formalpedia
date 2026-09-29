-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneArbitraryPortsRearrangeMod0
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:21:49.446198+00:00
-- url     : https://prove2.me/submissions/887c81f2-8d5d-4bba-a900-b424349b505f

import Mathlib

namespace CubicP3Partition

set_option maxRecDepth 100000


end CubicP3Partition

open CubicP3Partition
theorem solution
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

