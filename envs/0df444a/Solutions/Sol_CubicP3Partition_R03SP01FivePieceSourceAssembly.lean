-- Prove2me | solution 1 for CubicP3Partition.R03SP01FivePieceSourceAssembly
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:12.749861+00:00
-- url     : https://prove2.me/submissions/4d91b0ec-dc76-4c8b-8c44-674e6a6d726e

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

set_option maxRecDepth 100000


end CubicP3Partition

open CubicP3Partition
theorem solution
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

