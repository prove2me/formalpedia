-- Prove2me | solution 1 for FiniteSimpleGraph.exists_edge_maximal_extension__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:29:08.362191+00:00
-- url     : https://prove2.me/submissions/0ff4b38e-a91f-4ca7-b46c-b388d8b95f07

-- ID: 04530e67-a406-43c9-a9b5-30db75f9b07d | NAME: FiniteSimpleGraph.exists_edge_maximal_extension__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ G H : SimpleGraph V, H.edgeSet ⊆ G.edgeSet → P G → P H)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧ P L ∧
      (∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet → P M →
        M.edgeSet = L.edgeSet) := by
  classical
  let p : SimpleGraph V → Prop := fun H => P H ∧ K.edgeSet ⊆ H.edgeSet
  have hpK : p K := ⟨hK, by simp⟩
  obtain ⟨L, hKL, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := K) hpK)
  rcases hmax with ⟨hpL, hmax'⟩
  refine ⟨L, hpL.2, hpL.1, ?_⟩
  intro M hLM hPM
  have hle : L ≤ M := SimpleGraph.edgeSet_subset_edgeSet.mp hLM
  have hpM : p M := ⟨hPM, fun e he => hLM (hpL.2 he)⟩
  have hML : M.edgeSet ⊆ L.edgeSet := SimpleGraph.edgeSet_mono (hmax' hpM hle)
  exact le_antisymm hML hLM
