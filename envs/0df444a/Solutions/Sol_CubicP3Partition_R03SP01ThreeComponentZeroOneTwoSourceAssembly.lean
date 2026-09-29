-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeComponentZeroOneTwoSourceAssembly
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:30:46.717669+00:00
-- url     : https://prove2.me/submissions/f5b9b229-ee0d-471d-9dbd-a6db3249d49b

import Mathlib
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

