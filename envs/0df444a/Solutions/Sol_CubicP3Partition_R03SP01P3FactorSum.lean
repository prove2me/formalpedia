-- Prove2me | solution 1 for CubicP3Partition.R03SP01P3FactorSum
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:28:29.97138+00:00
-- url     : https://prove2.me/submissions/a3935fd6-3d3c-420d-aa3e-2781a1bfb389

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_654ea48678_r03_sp01_p3_factor_sum_gluing_candidate_v1

namespace CubicP3Partition

universe u
set_option maxHeartbeats 1000000

end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {A B : Type u} [Fintype A] [Fintype B]
    (GA : SimpleGraph A) (GB : SimpleGraph B)
    (G : SimpleGraph (A ⊕ B))
    (pA : P3Factor GA) (pB : P3Factor GB)
    (hA : ∀ {x y : A}, GA.Adj x y → G.Adj (Sum.inl x) (Sum.inl y))
    (hB : ∀ {x y : B}, GB.Adj x y → G.Adj (Sum.inr x) (Sum.inr y)) :
    Nonempty (P3Factor G) := by
  let blockEquiv : Fin (pA.blockCount + pB.blockCount) ≃
      Fin pA.blockCount ⊕ Fin pB.blockCount :=
    finSumFinEquiv.symm
  let sourceEquiv : (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃
      ((Fin pA.blockCount × Fin 3) ⊕ (Fin pB.blockCount × Fin 3)) :=
    (blockEquiv.prodCongr (Equiv.refl (Fin 3))).trans R03SP01SumProdDistrib
  let placeEquiv : ((Fin pA.blockCount × Fin 3) ⊕
      (Fin pB.blockCount × Fin 3)) ≃ (A ⊕ B) :=
    Equiv.sumCongr pA.place pB.place
  let place : (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃ (A ⊕ B) :=
    sourceEquiv.trans placeEquiv
  refine ⟨{
    blockCount := pA.blockCount + pB.blockCount
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    generalize hb : blockEquiv i = z
    cases z with
    | inl z =>
      have h := pA.edge01 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hA h
    | inr z =>
      have h := pB.edge01 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hB h
  · intro i
    generalize hb : blockEquiv i = z
    cases z with
    | inl z =>
      have h := pA.edge12 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hA h
    | inr z =>
      have h := pB.edge12 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hB h
