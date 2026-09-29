-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeComponent012PhaseZeroCrossRepairAssembly
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:30:44.886179+00:00
-- url     : https://prove2.me/submissions/2a39da09-b136-44ac-9993-fc58f49d801d

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

set_option maxRecDepth 100000

/-- Assemble five local families of ordered triples after an explicit target
bijection has identified their disjoint carriers with the ambient graph.  The
hypotheses are deliberately edge-local: four residual families and two
exceptional triples are checked directly in the target coordinates. -/
theorem R03SP01SixPieceSourceAssembly
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

#print axioms R03SP01ThreeComponent012PhaseZeroRearrange


/-- A cyclic coordinate order for the phase-zero chord repair.  The two
residual A intervals are followed by the six exceptional A slots
`N-1,0,d,d-2,d-1,d+1`, where `d=3+3*k`. -/
noncomputable def R03SP01ThreeComponent012PhaseZeroAIndex
    (k l : Nat) :
    (((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6))) ≃
      Fin (3 + (k + (1 + l)) * 3) := by
  let f :
      (((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6))) ≃
        (Fin 1 ⊕
          (Fin (k * 3) ⊕
            (Fin 4 ⊕ (Fin (l * 3) ⊕ Fin 1)))) :=
    { toFun := fun x =>
        match x with
        | Sum.inl r =>
            Sum.inr (Sum.inl (finProdFinEquiv r))
        | Sum.inr (Sum.inl r) =>
            Sum.inr (Sum.inr (Sum.inr (Sum.inl (finProdFinEquiv r))))
        | Sum.inr (Sum.inr s) =>
            if s = 0 then
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (0 : Fin 1))))
            else if s = 1 then
              Sum.inl (0 : Fin 1)
            else if s = 2 then
              Sum.inr (Sum.inr (Sum.inl (2 : Fin 4)))
            else if s = 3 then
              Sum.inr (Sum.inr (Sum.inl (0 : Fin 4)))
            else if s = 4 then
              Sum.inr (Sum.inr (Sum.inl (1 : Fin 4)))
            else
              Sum.inr (Sum.inr (Sum.inl (3 : Fin 4)))
      invFun := fun x =>
        match x with
        | Sum.inl _ => Sum.inr (Sum.inr (1 : Fin 6))
        | Sum.inr (Sum.inl r) =>
            Sum.inl (finProdFinEquiv.symm r)
        | Sum.inr (Sum.inr (Sum.inl s)) =>
            if s = 0 then
              Sum.inr (Sum.inr (3 : Fin 6))
            else if s = 1 then
              Sum.inr (Sum.inr (4 : Fin 6))
            else if s = 2 then
              Sum.inr (Sum.inr (2 : Fin 6))
            else
              Sum.inr (Sum.inr (5 : Fin 6))
        | Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) =>
            Sum.inr (Sum.inl (finProdFinEquiv.symm r))
        | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) =>
            Sum.inr (Sum.inr (0 : Fin 6))
      left_inv := by
        intro x
        rcases x with x | x
        · simp
        · rcases x with x | x
          · simp
          · fin_cases x <;> simp
      right_inv := by
        intro x
        rcases x with x | x
        · have hx : x = (0 : Fin 1) := Subsingleton.elim _ _
          subst x
          simp
        · rcases x with x | x
          · simpa using (finProdFinEquiv.right_inv x)
          · rcases x with x | x
            · fin_cases x <;> simp
            · rcases x with x | x
              · simpa using (finProdFinEquiv.right_inv x)
              · have hx : x = (0 : Fin 1) := Subsingleton.elim _ _
                subst x
                simp }
  let nC : (Fin (l * 3) ⊕ Fin 1) ≃ Fin (l * 3 + 1) :=
    finSumFinEquiv
  let nB : (Fin 4 ⊕ (Fin (l * 3) ⊕ Fin 1)) ≃
      Fin (4 + (l * 3 + 1)) :=
    (Equiv.sumCongr (Equiv.refl (Fin 4)) nC).trans finSumFinEquiv
  let nA : (Fin (k * 3) ⊕ (Fin 4 ⊕ (Fin (l * 3) ⊕ Fin 1))) ≃
      Fin (k * 3 + (4 + (l * 3 + 1))) :=
    (Equiv.sumCongr (Equiv.refl (Fin (k * 3))) nB).trans finSumFinEquiv
  let nTop : (Fin 1 ⊕ (Fin (k * 3) ⊕
      (Fin 4 ⊕ (Fin (l * 3) ⊕ Fin 1)))) ≃
      Fin (1 + (k * 3 + (4 + (l * 3 + 1)))) :=
    (Equiv.sumCongr (Equiv.refl (Fin 1)) nA).trans finSumFinEquiv
  let normalize : Fin (1 + (k * 3 + (4 + (l * 3 + 1)))) ≃
      Fin (3 + (k + (1 + l)) * 3) := finCongr (by omega)
  exact f.trans (nTop.trans normalize)

#print axioms R03SP01ThreeComponent012PhaseZeroAIndex


/-- Target equivalence for the phase-zero chord repair. -/
noncomputable def R03SP01ThreeComponent012PhaseZeroTargetMap
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C) :
    (((Fin k × Fin 3) ⊕
      ((Fin l × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3)))))) ≃
      (A ⊕ (B ⊕ C)) := by
  let aIndex :
      ((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6)) ≃
        Fin (3 + (k + (1 + l)) * 3) :=
    R03SP01ThreeComponent012PhaseZeroAIndex k l
  let bIndex : ((Fin b × Fin 3) ⊕ Fin 1) ≃ Fin (1 + b * 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 1))).trans
      ((Equiv.sumComm (Fin (b * 3)) (Fin 1)).trans
        (finSumFinEquiv (m := 1) (n := b * 3)))
  let cIndex : ((Fin c × Fin 3) ⊕ Fin 2) ≃ Fin (2 + c * 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans
      ((Equiv.sumComm (Fin (c * 3)) (Fin 2)).trans
        (finSumFinEquiv (m := 2) (n := c * 3)))
  let components :
      ((((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6)) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕ ((Fin c × Fin 3) ⊕ Fin 2)))) ≃
      (A ⊕ (B ⊕ C)) :=
    Equiv.sumCongr (aIndex.trans eA)
      (Equiv.sumCongr (bIndex.trans eB) (cIndex.trans eC))
  exact (R03SP01ThreeComponent012PhaseZeroRearrange k l b c).trans components

#print axioms R03SP01ThreeComponent012PhaseZeroTargetMap


lemma R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A1
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin k) (j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroTargetMap k l b c eA eB eC
      (Sum.inl (i, j)) =
      Sum.inl (eA ⟨1 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩) := by
  simp [R03SP01ThreeComponent012PhaseZeroTargetMap,
    R03SP01ThreeComponent012PhaseZeroRearrange,
    R03SP01ThreeComponent012PhaseZeroAIndex,
    finProdFinEquiv]

lemma R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A2
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin l) (j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroTargetMap k l b c eA eB eC
      (Sum.inr (Sum.inl (i, j))) =
      Sum.inl (eA ⟨3 + k * 3 + 2 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩) := by
  simp [R03SP01ThreeComponent012PhaseZeroTargetMap,
    R03SP01ThreeComponent012PhaseZeroRearrange,
    R03SP01ThreeComponent012PhaseZeroAIndex,
    finProdFinEquiv]
  omega

lemma R03SP01ThreeComponent012PhaseZeroTargetMap_apply_B
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin b) (j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroTargetMap k l b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inl (i, j)))) =
      Sum.inr (Sum.inl (eB ⟨1 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩)) := by
  simp [R03SP01ThreeComponent012PhaseZeroTargetMap,
    R03SP01ThreeComponent012PhaseZeroRearrange,
    R03SP01ThreeComponent012PhaseZeroAIndex,
    finProdFinEquiv]

lemma R03SP01ThreeComponent012PhaseZeroTargetMap_apply_C
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin c) (j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroTargetMap k l b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))) =
      Sum.inr (Sum.inr (eC ⟨2 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩)) := by
  simp [R03SP01ThreeComponent012PhaseZeroTargetMap,
    R03SP01ThreeComponent012PhaseZeroRearrange,
    R03SP01ThreeComponent012PhaseZeroAIndex,
    finProdFinEquiv]

lemma R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C) (i j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroTargetMap k l b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, j))))) =
      (match i, j with
      | 0, 0 => Sum.inl (eA ⟨3 + (k + (1 + l)) * 3 - 1, by omega⟩)
      | 0, 1 => Sum.inl (eA 0)
      | 0, 2 => Sum.inr (Sum.inl (eB 0))
      | 1, 0 => Sum.inl (eA ⟨3 + k * 3, by omega⟩)
      | 1, 1 => Sum.inr (Sum.inr (eC 0))
      | 1, 2 => Sum.inr (Sum.inr (eC 1))
      | 2, 0 => Sum.inl (eA ⟨1 + k * 3, by omega⟩)
      | 2, 1 => Sum.inl (eA ⟨2 + k * 3, by omega⟩)
      | 2, 2 => Sum.inl (eA ⟨4 + k * 3, by omega⟩)) := by
  fin_cases i <;> fin_cases j <;>
    (try simp [R03SP01ThreeComponent012PhaseZeroTargetMap,
      R03SP01ThreeComponent012PhaseZeroRearrange,
      R03SP01ThreeComponent012PhaseZeroAIndex,
      finProdFinEquiv])
  all_goals apply Fin.ext <;>
    norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + c * 3)] <;> omega

#print axioms R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A1
#print axioms R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A2
#print axioms R03SP01ThreeComponent012PhaseZeroTargetMap_apply_B
#print axioms R03SP01ThreeComponent012PhaseZeroTargetMap_apply_C
#print axioms R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc


/-- Phase-zero chord assembly.  The three exceptional source triples are
reordered so that their required pairs are the A-cycle wrap, the A--B and
A--C cross edges, an ordinary A-cycle edge, a C-cycle edge, and one explicit
A chord.  All cyclic presentations and cross/chord edges are hypotheses. -/
theorem R03SP01ThreeComponent012PhaseZeroChordAssembly
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (hAcycle : ∀ i : Fin (3 + (k + (1 + l)) * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (3 + (k + (1 + l)) * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (hBcycle : ∀ i : Fin (1 + b * 3),
      G.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨(i.val + 1) % (1 + b * 3),
          Nat.mod_lt _ (by omega)⟩))))
    (hCcycle : ∀ i : Fin (2 + c * 3),
      G.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨(i.val + 1) % (2 + c * 3),
          Nat.mod_lt _ (by omega)⟩))))
    (hAB : G.Adj (Sum.inl (eA 0))
      (Sum.inr (Sum.inl (eB 0))))
    (hAC : G.Adj (Sum.inl (eA ⟨3 + k * 3, by omega⟩))
      (Sum.inr (Sum.inr (eC 0))))
    (hChord : G.Adj (Sum.inl (eA ⟨2 + k * 3, by omega⟩))
      (Sum.inl (eA ⟨4 + k * 3, by omega⟩))) :
    Nonempty (P3Factor G) := by
  let target :=
    R03SP01ThreeComponent012PhaseZeroTargetMap k l b c eA eB eC
  have stepA : ∀ (i : Fin (3 + (k + (1 + l)) * 3))
      (h : i.val + 1 < 3 + (k + (1 + l)) * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨i.val + 1, h⟩)) := by
    intro i h
    have hh := hAcycle i
    have hm : (i.val + 1) % (3 + (k + (1 + l)) * 3) = i.val + 1 :=
      Nat.mod_eq_of_lt h
    simpa [hm] using hh
  have stepB : ∀ (i : Fin (1 + b * 3))
      (h : i.val + 1 < 1 + b * 3),
      G.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨i.val + 1, h⟩))) := by
    intro i h
    have hh := hBcycle i
    have hm : (i.val + 1) % (1 + b * 3) = i.val + 1 :=
      Nat.mod_eq_of_lt h
    simpa [hm] using hh
  have stepC : ∀ (i : Fin (2 + c * 3))
      (h : i.val + 1 < 2 + c * 3),
      G.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨i.val + 1, h⟩))) := by
    intro i h
    have hh := hCcycle i
    have hm : (i.val + 1) % (2 + c * 3) = i.val + 1 :=
      Nat.mod_eq_of_lt h
    simpa [hm] using hh
  have hA' : ∀ i : Fin k,
      G.Adj (target (Sum.inl (i, (0 : Fin 3))))
        (target (Sum.inl (i, (1 : Fin 3)))) ∧
      G.Adj (target (Sum.inl (i, (1 : Fin 3))))
        (target (Sum.inl (i, (2 : Fin 3)))) := by
    intro i
    let q0 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨1 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q1 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨1 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q2 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨1 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    constructor
    · have hh := stepA q0 (by
        dsimp [q0]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A1
        k l b c eA eB eC i 0,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A1
        k l b c eA eB eC i 1]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q0, q1, finProdFinEquiv] <;>
        omega
    · have hh := stepA q1 (by
        dsimp [q1]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A1
        k l b c eA eB eC i 1,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A1
        k l b c eA eB eC i 2]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q1, q2, finProdFinEquiv] <;>
        omega
  have hA2' : ∀ i : Fin l,
      G.Adj (target (Sum.inr (Sum.inl (i, (0 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (1 : Fin 3))))) ∧
      G.Adj (target (Sum.inr (Sum.inl (i, (1 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (2 : Fin 3))))) := by
    intro i
    let q0 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨3 + k * 3 + 2 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q1 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨3 + k * 3 + 2 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    constructor
    · have hh := stepA q0 (by
        dsimp [q0]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A2
        k l b c eA eB eC i 0,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A2
        k l b c eA eB eC i 1]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q0, q1, finProdFinEquiv] <;>
        omega
    · have hh := stepA q1 (by
        dsimp [q1]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A2
        k l b c eA eB eC i 1,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_A2
        k l b c eA eB eC i 2]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q1, finProdFinEquiv] <;>
        omega
  have hB' : ∀ i : Fin b,
      G.Adj (target (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3))))))
        (target (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))) ∧
      G.Adj (target (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))
        (target (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3)))))) := by
    intro i
    let q0 : Fin (1 + b * 3) :=
      ⟨1 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q1 : Fin (1 + b * 3) :=
      ⟨1 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q2 : Fin (1 + b * 3) :=
      ⟨1 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    constructor
    · have hh := stepB q0 (by
        dsimp [q0]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_B
        k l b c eA eB eC i 0,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_B
        k l b c eA eB eC i 1]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q0, q1, finProdFinEquiv] <;>
        omega
    · have hh := stepB q1 (by
        dsimp [q1]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_B
        k l b c eA eB eC i 1,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_B
        k l b c eA eB eC i 2]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q1, q2, finProdFinEquiv] <;>
        omega
  have hC' : ∀ i : Fin c,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))) ∧
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3))))))) := by
    intro i
    let q0 : Fin (2 + c * 3) :=
      ⟨2 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q1 : Fin (2 + c * 3) :=
      ⟨2 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q2 : Fin (2 + c * 3) :=
      ⟨2 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    constructor
    · have hh := stepC q0 (by
        dsimp [q0]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_C
        k l b c eA eB eC i 0,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_C
        k l b c eA eB eC i 1]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q0, q1, finProdFinEquiv] <;>
        omega
    · have hh := stepC q1 (by
        dsimp [q1]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_C
        k l b c eA eB eC i 1,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_C
        k l b c eA eB eC i 2]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q1, q2, finProdFinEquiv] <;>
        omega
  have hWrapA : G.Adj
      (Sum.inl (eA ⟨3 + (k + (1 + l)) * 3 - 1, by omega⟩))
      (Sum.inl (eA 0)) := by
    have hh := hAcycle
      (⟨3 + (k + (1 + l)) * 3 - 1, by omega⟩ :
        Fin (3 + (k + (1 + l)) * 3))
    have hidx :
        (⟨(3 + (k + (1 + l)) * 3 - 1 + 1) %
            (3 + (k + (1 + l)) * 3),
          Nat.mod_lt _ (by omega)⟩ :
          Fin (3 + (k + (1 + l)) * 3)) = 0 := by
      apply Fin.ext
      change (3 + (k + (1 + l)) * 3 - 1 + 1) %
          (3 + (k + (1 + l)) * 3) = 0
      have he : 3 + (k + (1 + l)) * 3 - 1 + 1 =
          3 + (k + (1 + l)) * 3 := by omega
      rw [he, Nat.mod_self]
    rw [hidx] at hh
    simpa using hh
  have hAshort : G.Adj
      (Sum.inl (eA ⟨1 + k * 3, by omega⟩))
      (Sum.inl (eA ⟨2 + k * 3, by omega⟩)) := by
    have hh := stepA ⟨1 + k * 3, by
      simp [Nat.add_mul]
      omega⟩ (by
      simp [Nat.add_mul]
      omega)
    convert hh using 1 <;>
      congr 1 <;>
      (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
      congr 1 <;>
      apply Fin.ext <;>
      simp <;>
      omega
  have hC01 : G.Adj
      (Sum.inr (Sum.inr (eC 0)))
      (Sum.inr (Sum.inr (eC 1))) := by
    have hh := stepC ⟨0, by omega⟩ (by
      simp
      omega)
    convert hh using 1 <;>
      congr 1 <;>
      (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
      congr 1 <;>
      apply Fin.ext <;>
      norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + c * 3)]
  have hExc01 : ∀ i : Fin 3,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))) := by
    intro i
    fin_cases i
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 0 0,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 0 1]
      exact hWrapA
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 1 0,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 1 1]
      exact hAC
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 2 0,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 2 1]
      exact hAshort
  have hExc12 : ∀ i : Fin 3,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3))))))) := by
    intro i
    fin_cases i
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 0 1,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 0 2]
      exact hAB
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 1 1,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 1 2]
      exact hC01
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 2 1,
        R03SP01ThreeComponent012PhaseZeroTargetMap_apply_exc
        k l b c eA eB eC 2 2]
      exact hChord
  exact R03SP01SixPieceSourceAssembly G k l b c target
    hA' hA2' hB' hC' hExc01 hExc12

#print axioms R03SP01ThreeComponent012PhaseZeroChordAssembly


/-- Reorder the phase-zero exceptional cells for a cross-edge repair.  The
source permutation sends the cells to the existing six-slot grouping in the
order needed by the new exceptional triples. -/
noncomputable def R03SP01ThreeComponent012PhaseZeroCrossRepairRearrange
    (k l b c : Nat) :
    (((Fin k × Fin 3) ⊕
      ((Fin l × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3)))))) ≃
      ((((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6)) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕ ((Fin c × Fin 3) ⊕ Fin 2)))) := by
  let p : (Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3) := by
    let f : (Fin 3 × Fin 3) → (Fin 3 × Fin 3) := fun q =>
      match q.1, q.2 with
      | 0, 0 => (0, 0)
      | 0, 1 => (0, 1)
      | 0, 2 => (1, 0)
      | 1, 0 => (2, 0)
      | 1, 1 => (2, 1)
      | 1, 2 => (0, 2)
      | 2, 0 => (2, 2)
      | 2, 1 => (1, 1)
      | 2, 2 => (1, 2)
    let g : (Fin 3 × Fin 3) → (Fin 3 × Fin 3) := fun q =>
      match q.1, q.2 with
      | 0, 0 => (0, 0)
      | 0, 1 => (0, 1)
      | 0, 2 => (1, 2)
      | 1, 0 => (0, 2)
      | 1, 1 => (2, 1)
      | 1, 2 => (2, 2)
      | 2, 0 => (1, 0)
      | 2, 1 => (1, 1)
      | 2, 2 => (2, 0)
    exact {
      toFun := f
      invFun := g
      left_inv := by
        intro q
        rcases q with ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> simp [f, g]
      right_inv := by
        intro q
        rcases q with ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> simp [f, g] }
  let sourcePerm :
      (((Fin k × Fin 3) ⊕
        ((Fin l × Fin 3) ⊕
          ((Fin b × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3)))))) ≃
      (((Fin k × Fin 3) ⊕
        ((Fin l × Fin 3) ⊕
          ((Fin b × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3)))))) :=
    Equiv.sumCongr (Equiv.refl (Fin k × Fin 3))
      (Equiv.sumCongr (Equiv.refl (Fin l × Fin 3))
        (Equiv.sumCongr (Equiv.refl (Fin b × Fin 3))
          (Equiv.sumCongr (Equiv.refl (Fin c × Fin 3)) p)))
  exact sourcePerm.trans
    (R03SP01ThreeComponent012PhaseZeroRearrange k l b c)

#print axioms R03SP01ThreeComponent012PhaseZeroCrossRepairRearrange

/-- A finite A-coordinate order for the phase-zero cross-edge repair.  Its
exceptional A positions are `N-2,N-1,0,d-2,d-1,d`, while the second residual
interval is `d+1,...,N-3`, where `d=3+3*k`. -/
noncomputable def R03SP01ThreeComponent012PhaseZeroCrossRepairAIndex
    (k l : Nat) :
    (((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6))) ≃
      Fin (3 + (k + (1 + l)) * 3) := by
  let f :
      (((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6))) ≃
        (Fin 1 ⊕
          (Fin (k * 3) ⊕
            (Fin 3 ⊕ (Fin (l * 3) ⊕ Fin 2)))) :=
    { toFun := fun x =>
        match x with
        | Sum.inl r =>
            Sum.inr (Sum.inl (finProdFinEquiv r))
        | Sum.inr (Sum.inl r) =>
            Sum.inr (Sum.inr (Sum.inr (Sum.inl (finProdFinEquiv r))))
        | Sum.inr (Sum.inr s) =>
            if s = 0 then
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (0 : Fin 2))))
            else if s = 1 then
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (1 : Fin 2))))
            else if s = 2 then
              Sum.inl (0 : Fin 1)
            else if s = 3 then
              Sum.inr (Sum.inr (Sum.inl (0 : Fin 3)))
            else if s = 4 then
              Sum.inr (Sum.inr (Sum.inl (1 : Fin 3)))
            else
              Sum.inr (Sum.inr (Sum.inl (2 : Fin 3)))
      invFun := fun x =>
        match x with
        | Sum.inl _ => Sum.inr (Sum.inr (2 : Fin 6))
        | Sum.inr (Sum.inl r) =>
            Sum.inl (finProdFinEquiv.symm r)
        | Sum.inr (Sum.inr (Sum.inl s)) =>
            if s = 0 then
              Sum.inr (Sum.inr (3 : Fin 6))
            else if s = 1 then
              Sum.inr (Sum.inr (4 : Fin 6))
            else
              Sum.inr (Sum.inr (5 : Fin 6))
        | Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) =>
            Sum.inr (Sum.inl (finProdFinEquiv.symm r))
        | Sum.inr (Sum.inr (Sum.inr (Sum.inr s))) =>
            if s = 0 then
              Sum.inr (Sum.inr (0 : Fin 6))
            else
              Sum.inr (Sum.inr (1 : Fin 6))
      left_inv := by
        intro x
        rcases x with x | x
        · simp
        · rcases x with x | x
          · simp
          · fin_cases x <;> simp
      right_inv := by
        intro x
        rcases x with x | x
        · have hx : x = (0 : Fin 1) := Subsingleton.elim _ _
          subst x
          simp
        · rcases x with x | x
          · simpa using (finProdFinEquiv.right_inv x)
          · rcases x with x | x
            · fin_cases x <;> simp
            · rcases x with x | x
              · simpa using (finProdFinEquiv.right_inv x)
              · fin_cases x <;> simp }
  let nD : (Fin (l * 3) ⊕ Fin 2) ≃ Fin (l * 3 + 2) :=
    finSumFinEquiv
  let nC : (Fin 3 ⊕ (Fin (l * 3) ⊕ Fin 2)) ≃
      Fin (3 + (l * 3 + 2)) :=
    (Equiv.sumCongr (Equiv.refl (Fin 3)) nD).trans finSumFinEquiv
  let nB : (Fin (k * 3) ⊕ (Fin 3 ⊕ (Fin (l * 3) ⊕ Fin 2))) ≃
      Fin (k * 3 + (3 + (l * 3 + 2))) :=
    (Equiv.sumCongr (Equiv.refl (Fin (k * 3))) nC).trans finSumFinEquiv
  let nTop : (Fin 1 ⊕
      (Fin (k * 3) ⊕ (Fin 3 ⊕ (Fin (l * 3) ⊕ Fin 2)))) ≃
      Fin (1 + (k * 3 + (3 + (l * 3 + 2)))) :=
    (Equiv.sumCongr (Equiv.refl (Fin 1)) nB).trans finSumFinEquiv
  let normalize : Fin (1 + (k * 3 + (3 + (l * 3 + 2)))) ≃
      Fin (3 + (k + (1 + l)) * 3) := finCongr (by omega)
  exact f.trans (nTop.trans normalize)

#print axioms R03SP01ThreeComponent012PhaseZeroCrossRepairAIndex

/-- Target equivalence for the phase-zero cross-edge repair. -/
noncomputable def R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C) :
    (((Fin k × Fin 3) ⊕
      ((Fin l × Fin 3) ⊕
        ((Fin b × Fin 3) ⊕
          ((Fin c × Fin 3) ⊕ (Fin 3 × Fin 3)))))) ≃
      (A ⊕ (B ⊕ C)) := by
  let aIndex :
      ((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6)) ≃
        Fin (3 + (k + (1 + l)) * 3) :=
    R03SP01ThreeComponent012PhaseZeroCrossRepairAIndex k l
  let bIndex : ((Fin b × Fin 3) ⊕ Fin 1) ≃ Fin (1 + b * 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 1))).trans
      ((Equiv.sumComm (Fin (b * 3)) (Fin 1)).trans
        (finSumFinEquiv (m := 1) (n := b * 3)))
  let cIndex : ((Fin c × Fin 3) ⊕ Fin 2) ≃ Fin (2 + c * 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans
      ((Equiv.sumComm (Fin (c * 3)) (Fin 2)).trans
        (finSumFinEquiv (m := 2) (n := c * 3)))
  let components :
      ((((Fin k × Fin 3) ⊕ ((Fin l × Fin 3) ⊕ Fin 6)) ⊕
        (((Fin b × Fin 3) ⊕ Fin 1) ⊕ ((Fin c × Fin 3) ⊕ Fin 2)))) ≃
      (A ⊕ (B ⊕ C)) :=
    Equiv.sumCongr (aIndex.trans eA)
      (Equiv.sumCongr (bIndex.trans eB) (cIndex.trans eC))
  exact
    (R03SP01ThreeComponent012PhaseZeroCrossRepairRearrange k l b c).trans
      components

#print axioms R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap

lemma R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A1
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin k) (j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap k l b c eA eB eC
      (Sum.inl (i, j)) =
      Sum.inl (eA ⟨1 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩) := by
  simp [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap,
    R03SP01ThreeComponent012PhaseZeroCrossRepairRearrange,
    R03SP01ThreeComponent012PhaseZeroCrossRepairAIndex,
    R03SP01ThreeComponent012PhaseZeroRearrange,
    finProdFinEquiv]

lemma R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A2
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin l) (j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap k l b c eA eB eC
      (Sum.inr (Sum.inl (i, j))) =
      Sum.inl (eA ⟨3 + k * 3 + 1 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩) := by
  simp [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap,
    R03SP01ThreeComponent012PhaseZeroCrossRepairRearrange,
    R03SP01ThreeComponent012PhaseZeroCrossRepairAIndex,
    R03SP01ThreeComponent012PhaseZeroRearrange,
    finProdFinEquiv]
  omega

lemma R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_B
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin b) (j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap k l b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inl (i, j)))) =
      Sum.inr (Sum.inl (eB ⟨1 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩)) := by
  simp [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap,
    R03SP01ThreeComponent012PhaseZeroCrossRepairRearrange,
    R03SP01ThreeComponent012PhaseZeroRearrange,
    R03SP01ThreeComponent012PhaseZeroCrossRepairAIndex,
    finProdFinEquiv]

lemma R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_C
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (i : Fin c) (j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap k l b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))) =
      Sum.inr (Sum.inr (eC ⟨2 + (finProdFinEquiv (i, j)).val, by
        simp [finProdFinEquiv]
        omega⟩)) := by
  simp [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap,
    R03SP01ThreeComponent012PhaseZeroCrossRepairRearrange,
    R03SP01ThreeComponent012PhaseZeroCrossRepairAIndex,
    R03SP01ThreeComponent012PhaseZeroRearrange,
    finProdFinEquiv]

lemma R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C) (i j : Fin 3) :
    R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap k l b c eA eB eC
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, j))))) =
      (match i, j with
      | 0, 0 => Sum.inl (eA ⟨3 + (k + (1 + l)) * 3 - 2, by omega⟩)
      | 0, 1 => Sum.inl (eA ⟨3 + (k + (1 + l)) * 3 - 1, by omega⟩)
      | 0, 2 => Sum.inl (eA 0)
      | 1, 0 => Sum.inl (eA ⟨1 + k * 3, by omega⟩)
      | 1, 1 => Sum.inl (eA ⟨2 + k * 3, by omega⟩)
      | 1, 2 => Sum.inr (Sum.inl (eB 0))
      | 2, 0 => Sum.inl (eA ⟨3 + k * 3, by omega⟩)
      | 2, 1 => Sum.inr (Sum.inr (eC 0))
      | 2, 2 => Sum.inr (Sum.inr (eC 1))) := by
  fin_cases i <;> fin_cases j <;>
    (try simp [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap,
      R03SP01ThreeComponent012PhaseZeroCrossRepairRearrange,
      R03SP01ThreeComponent012PhaseZeroCrossRepairAIndex,
      R03SP01ThreeComponent012PhaseZeroRearrange,
      finProdFinEquiv])
  all_goals apply Fin.ext <;>
    norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + c * 3)] <;> omega

#print axioms R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A1
#print axioms R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A2
#print axioms R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_B
#print axioms R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_C
#print axioms R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc


end CubicP3Partition

open CubicP3Partition
universe u
open SimpleGraph
theorem solution
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (k l b c : Nat)
    (eA : Fin (3 + (k + (1 + l)) * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (2 + c * 3) ≃ C)
    (hAcycle : ∀ i : Fin (3 + (k + (1 + l)) * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (3 + (k + (1 + l)) * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (hBcycle : ∀ i : Fin (1 + b * 3),
      G.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨(i.val + 1) % (1 + b * 3),
          Nat.mod_lt _ (by omega)⟩))))
    (hCcycle : ∀ i : Fin (2 + c * 3),
      G.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨(i.val + 1) % (2 + c * 3),
          Nat.mod_lt _ (by omega)⟩))))
    (hAB : G.Adj (Sum.inl (eA ⟨2 + k * 3, by omega⟩))
      (Sum.inr (Sum.inl (eB 0))))
    (hAC : G.Adj (Sum.inl (eA ⟨3 + k * 3, by omega⟩))
      (Sum.inr (Sum.inr (eC 0)))) :
    Nonempty (P3Factor G) := by
  let target :=
    R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap k l b c eA eB eC
  have stepA : ∀ (i : Fin (3 + (k + (1 + l)) * 3))
      (h : i.val + 1 < 3 + (k + (1 + l)) * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨i.val + 1, h⟩)) := by
    intro i h
    have hh := hAcycle i
    have hm : (i.val + 1) % (3 + (k + (1 + l)) * 3) = i.val + 1 :=
      Nat.mod_eq_of_lt h
    simpa [hm] using hh
  have stepB : ∀ (i : Fin (1 + b * 3))
      (h : i.val + 1 < 1 + b * 3),
      G.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨i.val + 1, h⟩))) := by
    intro i h
    have hh := hBcycle i
    have hm : (i.val + 1) % (1 + b * 3) = i.val + 1 :=
      Nat.mod_eq_of_lt h
    simpa [hm] using hh
  have stepC : ∀ (i : Fin (2 + c * 3))
      (h : i.val + 1 < 2 + c * 3),
      G.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨i.val + 1, h⟩))) := by
    intro i h
    have hh := hCcycle i
    have hm : (i.val + 1) % (2 + c * 3) = i.val + 1 :=
      Nat.mod_eq_of_lt h
    simpa [hm] using hh
  have hA' : ∀ i : Fin k,
      G.Adj (target (Sum.inl (i, (0 : Fin 3))))
        (target (Sum.inl (i, (1 : Fin 3)))) ∧
      G.Adj (target (Sum.inl (i, (1 : Fin 3))))
        (target (Sum.inl (i, (2 : Fin 3)))) := by
    intro i
    let q0 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨1 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q1 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨1 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q2 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨1 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    constructor
    · have hh := stepA q0 (by
        dsimp [q0]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A1
        k l b c eA eB eC i 0,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A1
        k l b c eA eB eC i 1]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q0, q1, finProdFinEquiv] <;>
        omega
    · have hh := stepA q1 (by
        dsimp [q1]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A1
        k l b c eA eB eC i 1,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A1
        k l b c eA eB eC i 2]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q1, q2, finProdFinEquiv] <;>
        omega
  have hA2' : ∀ i : Fin l,
      G.Adj (target (Sum.inr (Sum.inl (i, (0 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (1 : Fin 3))))) ∧
      G.Adj (target (Sum.inr (Sum.inl (i, (1 : Fin 3)))))
        (target (Sum.inr (Sum.inl (i, (2 : Fin 3))))) := by
    intro i
    let q0 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨3 + k * 3 + 1 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q1 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨3 + k * 3 + 1 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q2 : Fin (3 + (k + (1 + l)) * 3) :=
      ⟨3 + k * 3 + 1 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    constructor
    · have hh := stepA q0 (by
        dsimp [q0]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A2
        k l b c eA eB eC i 0,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A2
        k l b c eA eB eC i 1]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q0, q1, finProdFinEquiv] <;>
        omega
    · have hh := stepA q1 (by
        dsimp [q1]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A2
        k l b c eA eB eC i 1,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_A2
        k l b c eA eB eC i 2]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q1, q2, finProdFinEquiv] <;>
        omega
  have hB' : ∀ i : Fin b,
      G.Adj (target (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3))))))
        (target (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))) ∧
      G.Adj (target (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))
        (target (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3)))))) := by
    intro i
    let q0 : Fin (1 + b * 3) :=
      ⟨1 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q1 : Fin (1 + b * 3) :=
      ⟨1 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q2 : Fin (1 + b * 3) :=
      ⟨1 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    constructor
    · have hh := stepB q0 (by
        dsimp [q0]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_B
        k l b c eA eB eC i 0,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_B
        k l b c eA eB eC i 1]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q0, q1, finProdFinEquiv] <;>
        omega
    · have hh := stepB q1 (by
        dsimp [q1]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_B
        k l b c eA eB eC i 1,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_B
        k l b c eA eB eC i 2]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q1, q2, finProdFinEquiv] <;>
        omega
  have hC' : ∀ i : Fin c,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3))))))) ∧
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, (2 : Fin 3))))))) := by
    intro i
    let q0 : Fin (2 + c * 3) :=
      ⟨2 + (finProdFinEquiv (i, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q1 : Fin (2 + c * 3) :=
      ⟨2 + (finProdFinEquiv (i, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    let q2 : Fin (2 + c * 3) :=
      ⟨2 + (finProdFinEquiv (i, (2 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
    constructor
    · have hh := stepC q0 (by
        dsimp [q0]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_C
        k l b c eA eB eC i 0,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_C
        k l b c eA eB eC i 1]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q0, q1, finProdFinEquiv] <;>
        omega
    · have hh := stepC q1 (by
        dsimp [q1]
        simp [finProdFinEquiv]
        omega)
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_C
        k l b c eA eB eC i 1,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_C
        k l b c eA eB eC i 2]
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [q1, q2, finProdFinEquiv] <;>
        omega
  have hExc01 : ∀ i : Fin 3,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (0 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3))))))) := by
    intro i
    fin_cases i
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 0 0,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 0 1]
      have hcond :
          (3 + (k + (1 + l)) * 3 - 2) + 1 <
            3 + (k + (1 + l)) * 3 := by omega
      change G.Adj
        (Sum.inl (eA ⟨3 + (k + (1 + l)) * 3 - 2, by omega⟩))
        (Sum.inl (eA ⟨3 + (k + (1 + l)) * 3 - 1, by omega⟩))
      have hh := stepA
        (⟨3 + (k + (1 + l)) * 3 - 2, by omega⟩ :
          Fin (3 + (k + (1 + l)) * 3)) (by simpa using hcond)
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [Nat.add_mul] <;>
        omega
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 1 0,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 1 1]
      have hcond : 1 + k * 3 + 1 <
          3 + (k + (1 + l)) * 3 := by omega
      change G.Adj
        (Sum.inl (eA ⟨1 + k * 3, by omega⟩))
        (Sum.inl (eA ⟨2 + k * 3, by omega⟩))
      have hh := stepA
        (⟨1 + k * 3, by omega⟩ :
          Fin (3 + (k + (1 + l)) * 3)) (by simpa using hcond)
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        simp [Nat.add_mul] <;>
        omega
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 2 0,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 2 1]
      exact hAC
  have hExc12 : ∀ i : Fin 3,
      G.Adj (target
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (1 : Fin 3)))))))
        (target
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, (2 : Fin 3))))))) := by
    intro i
    fin_cases i
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 0 1,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 0 2]
      have hh := hAcycle
        (⟨3 + (k + (1 + l)) * 3 - 1, by omega⟩ :
          Fin (3 + (k + (1 + l)) * 3))
      have hidx :
          (⟨(3 + (k + (1 + l)) * 3 - 1 + 1) %
              (3 + (k + (1 + l)) * 3),
            Nat.mod_lt _ (by omega)⟩ :
            Fin (3 + (k + (1 + l)) * 3)) = 0 := by
        apply Fin.ext
        change (3 + (k + (1 + l)) * 3 - 1 + 1) %
            (3 + (k + (1 + l)) * 3) = 0
        have he : 3 + (k + (1 + l)) * 3 - 1 + 1 =
            3 + (k + (1 + l)) * 3 := by omega
        rw [he, Nat.mod_self]
      rw [hidx] at hh
      simpa using hh
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 1 1,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 1 2]
      change G.Adj
        (Sum.inl (eA ⟨2 + k * 3, by omega⟩))
        (Sum.inr (Sum.inl (eB 0)))
      exact hAB
    · dsimp [target]
      rw [R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 2 1,
        R03SP01ThreeComponent012PhaseZeroCrossRepairTargetMap_apply_exc
        k l b c eA eB eC 2 2]
      change G.Adj
        (Sum.inr (Sum.inr (eC 0)))
        (Sum.inr (Sum.inr (eC 1)))
      have hh := stepC ⟨0, by omega⟩ (by
        simp
        omega)
      convert hh using 1 <;>
        congr 1 <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq]) <;>
        congr 1 <;>
        apply Fin.ext <;>
        norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + c * 3)]
  exact R03SP01SixPieceSourceAssembly G k l b c target
    hA' hA2' hB' hC' hExc01 hExc12

