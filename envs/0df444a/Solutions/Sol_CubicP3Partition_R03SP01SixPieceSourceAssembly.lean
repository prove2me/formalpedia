-- Prove2me | solution 1 for CubicP3Partition.R03SP01SixPieceSourceAssembly
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:30:28.331156+00:00
-- url     : https://prove2.me/submissions/d99e828c-a8a5-4417-bb1c-70da0c541cd3

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

set_option maxRecDepth 100000


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (a k1 k2 c : Nat)
    (target :
      (((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3))))) ≃
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
    (hExc01 : ∀ i : Fin 3,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))))
    (hExc12 : ∀ i : Fin 3,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3)))))))) :
    Nonempty (P3Factor G) := by
  let rest1 := k1 + (k2 + (c + 3))
  let rest2 := k2 + (c + 3)
  let rest3 := c + 3
  let blockSum : Fin (a + (k1 + (k2 + (c + 3)))) ≃
      Fin a ⊕ (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 3))) :=
    finSumFinEquiv.symm.trans
      (Equiv.sumCongr (Equiv.refl (Fin a))
        (finSumFinEquiv.symm.trans
          (Equiv.sumCongr (Equiv.refl (Fin k1))
            (finSumFinEquiv.symm.trans
              (Equiv.sumCongr (Equiv.refl (Fin k2))
                finSumFinEquiv.symm)))))
  let dA : (Fin a ⊕ (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 3))) ) × Fin 3 ≃
      (Fin a × Fin 3) ⊕
        ((Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 3))) × Fin 3) :=
    Equiv.sumProdDistrib (Fin a)
      (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 3))) (Fin 3)
  let dB : (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 3))) × Fin 3 ≃
      (Fin k1 × Fin 3) ⊕
        ((Fin k2 ⊕ (Fin c ⊕ Fin 3)) × Fin 3) :=
    Equiv.sumProdDistrib (Fin k1) (Fin k2 ⊕ (Fin c ⊕ Fin 3)) (Fin 3)
  let dC : (Fin k2 ⊕ (Fin c ⊕ Fin 3)) × Fin 3 ≃
      (Fin k2 × Fin 3) ⊕ ((Fin c ⊕ Fin 3) × Fin 3) :=
    Equiv.sumProdDistrib (Fin k2) (Fin c ⊕ Fin 3) (Fin 3)
  let dD : (Fin c ⊕ Fin 3) × Fin 3 ≃
      (Fin c × Fin 3) ⊕ (Fin 3 × Fin 3) :=
    Equiv.sumProdDistrib (Fin c) (Fin 3) (Fin 3)
  let distributed :
      (Fin a ⊕ (Fin k1 ⊕ (Fin k2 ⊕ (Fin c ⊕ Fin 3)))) × Fin 3 ≃
      ((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3))))) :=
    dA.trans (Equiv.sumCongr (Equiv.refl (Fin a × Fin 3))
      (dB.trans (Equiv.sumCongr (Equiv.refl (Fin k1 × Fin 3))
        (dC.trans (Equiv.sumCongr (Equiv.refl (Fin k2 × Fin 3)) dD)))))
  let blockToSource :
      (Fin (a + (k1 + (k2 + (c + 3)))) × Fin 3) ≃
      ((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3))))) :=
    (blockSum.prodCongr (Equiv.refl (Fin 3))).trans distributed
  let place : (Fin (a + (k1 + (k2 + (c + 3)))) × Fin 3) ≃
      (A ⊕ (B ⊕ C)) := blockToSource.trans target
  refine ⟨{
    blockCount := a + (k1 + (k2 + (c + 3)))
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
        · refine Fin.addCases (m := c) (n := 3) (fun j => ?_) (fun j => ?_) i
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
            · have h := hExc01 2
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
        · refine Fin.addCases (m := c) (n := 3) (fun j => ?_) (fun j => ?_) i
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
            · have h := hExc12 2
              simpa [place, blockToSource, blockSum, distributed, dA, dB, dC, dD,
                Fin.addCases_left, Fin.addCases_right, Equiv.trans_apply,
                finProdFinEquiv] using h



open SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Reorganize three phase-zero exceptional triples into six A slots, one B
slot, and two C slots.  The map is only a finite permutation; it carries no
edge information. -/
noncomputable def R03SP01ThreeComponent012PhaseZeroRearrange
    (k l b c : Nat) :
    (((Fin k × Fin 3) ⊕
      ((Fin l × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3)))))) ≃
      ((((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6)) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕ ((Fin c × Fin 3) ⊕ Fin 2)))) := by
  let f :
      (((Fin k × Fin 3) ⊕
        ((Fin l × Fin 3) ⊕
          ((Fin b × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3)))))) →
      ((((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6)) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕ ((Fin c × Fin 3) ⊕ Fin 2)))) := fun x =>
    match x with
    | Sum.inl x => Sum.inl (Sum.inl x)
    | Sum.inr (Sum.inl x) => Sum.inl (Sum.inr (Sum.inl x))
    | Sum.inr (Sum.inr (Sum.inl x)) => Sum.inr (Sum.inl (Sum.inl x))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) =>
        Sum.inr (Sum.inr (Sum.inl x))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) =>
        if q.1 = 0 then
          if q.2 = 0 then
            Sum.inl (Sum.inr (Sum.inr (0 : Fin 6)))
          else if q.2 = 1 then
            Sum.inl (Sum.inr (Sum.inr (1 : Fin 6)))
          else
            Sum.inr (Sum.inl (Sum.inr (0 : Fin 1)))
        else if q.1 = 1 then
          if q.2 = 0 then
            Sum.inl (Sum.inr (Sum.inr (2 : Fin 6)))
          else if q.2 = 1 then
            Sum.inr (Sum.inr (Sum.inr (0 : Fin 2)))
          else
            Sum.inr (Sum.inr (Sum.inr (1 : Fin 2)))
        else
          if q.2 = 0 then
            Sum.inl (Sum.inr (Sum.inr (3 : Fin 6)))
          else if q.2 = 1 then
            Sum.inl (Sum.inr (Sum.inr (4 : Fin 6)))
          else
            Sum.inl (Sum.inr (Sum.inr (5 : Fin 6)))
  let g :
      ((((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6)) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕ ((Fin c × Fin 3) ⊕ Fin 2)))) →
      (((Fin k × Fin 3) ⊕
        ((Fin l × Fin 3) ⊕
          ((Fin b × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3)))))) := fun x =>
    match x with
    | Sum.inl (Sum.inl x) => Sum.inl x
    | Sum.inl (Sum.inr (Sum.inl x)) => Sum.inr (Sum.inl x)
    | Sum.inl (Sum.inr (Sum.inr s)) =>
        if s = 0 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 0))))
        else if s = 1 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 1))))
        else if s = 2 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 0))))
        else if s = 3 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (2, 0))))
        else if s = 4 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (2, 1))))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (2, 2))))
    | Sum.inr (Sum.inl (Sum.inl x)) =>
        Sum.inr (Sum.inr (Sum.inl x))
    | Sum.inr (Sum.inl (Sum.inr _)) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (0, 2))))
    | Sum.inr (Sum.inr (Sum.inl x)) =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))
    | Sum.inr (Sum.inr (Sum.inr s)) =>
        if s = 0 then
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 1))))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (1, 2))))
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
      | inr x =>
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

