-- Prove2me | solution 1 for CubicP3Partition.R03SP01GlueP3FactorTwoExceptionalBlocks
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T09:58:41.59386+00:00
-- url     : https://prove2.me/submissions/b1822640-b471-4d88-a532-db1ce82d838d

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_e518dcb8e8_r03_sp01_glue_factor_two_exceptions_candidate_v1

namespace CubicP3Partition

universe u

end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V W : Type u} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (p : P3Factor H)
    (target : ((Fin p.blockCount × Fin 3) ⊕ (Fin 2 × Fin 3)) ≃ V)
    (hlocal : ∀ {x y : W}, H.Adj x y →
      G.Adj (target (Sum.inl (p.place.symm x)))
        (target (Sum.inl (p.place.symm y))))
    (hex01 : ∀ i : Fin 2,
      G.Adj (target (Sum.inr (i, (0 : Fin 3))))
        (target (Sum.inr (i, (1 : Fin 3)))))
    (hex12 : ∀ i : Fin 2,
      G.Adj (target (Sum.inr (i, (1 : Fin 3))))
        (target (Sum.inr (i, (2 : Fin 3))))) :
    Nonempty (P3Factor G) := by
  let blockEquiv : Fin (p.blockCount + 2) ≃ Fin p.blockCount ⊕ Fin 2 :=
    finSumFinEquiv.symm
  let sourceEquiv : (Fin (p.blockCount + 2) × Fin 3) ≃
      ((Fin p.blockCount × Fin 3) ⊕ (Fin 2 × Fin 3)) :=
    (blockEquiv.prodCongr (Equiv.refl (Fin 3))).trans
      R03SP01GlueTwoExceptionsSumProdDistrib
  let place : (Fin (p.blockCount + 2) × Fin 3) ≃ V :=
    sourceEquiv.trans target
  refine ⟨{
    blockCount := p.blockCount + 2
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    generalize hb : blockEquiv i = z
    cases z with
    | inl z =>
      have hp := p.edge01 z
      have hl := hlocal hp
      simpa [place, sourceEquiv, blockEquiv,
        R03SP01GlueTwoExceptionsSumProdDistrib, hb] using hl
    | inr z =>
      have he := hex01 z
      simpa [place, sourceEquiv, blockEquiv,
        R03SP01GlueTwoExceptionsSumProdDistrib, hb] using he
  · intro i
    generalize hb : blockEquiv i = z
    cases z with
    | inl z =>
      have hp := p.edge12 z
      have hl := hlocal hp
      simpa [place, sourceEquiv, blockEquiv,
        R03SP01GlueTwoExceptionsSumProdDistrib, hb] using hl
    | inr z =>
      have he := hex12 z
      simpa [place, sourceEquiv, blockEquiv,
        R03SP01GlueTwoExceptionsSumProdDistrib, hb] using he
