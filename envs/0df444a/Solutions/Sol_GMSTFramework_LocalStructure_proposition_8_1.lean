-- Prove2me | solution 1 for GMSTFramework.LocalStructure.proposition_8_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:59:41.434811+00:00
-- url     : https://prove2.me/submissions/f00919a4-1bfe-4ca4-aa9b-4020c481e80d

import Definitions.Def_GMSTFramework_LocalStructure_Societies

open scoped Classical
open GMSTFramework.LocalStructure

theorem solution :
    ¬ (∀ k : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Ω : List V),
      Ω.Nodup → DepthLE (⊤ : G.Subgraph) Ω k →
        ∃ D : LinearDecomposition (⊤ : G.Subgraph) Ω, D.AdhesionLE k) := by
  intro h
  have hdepth : DepthLE (⊤ : (⊥ : SimpleGraph (Fin 1)).Subgraph) ([] : List (Fin 1)) 0 := by
    intro n T
    by_contra hn
    have hpos : 0 < n := Nat.pos_of_ne_zero (by omega)
    have hpath := T.ΩPath ⟨0, hpos⟩
    rcases hpath with ⟨hs, _, _⟩
    simp at hs
  rcases h 0 (⊥ : SimpleGraph (Fin 1)) ([] : List (Fin 1)) List.nodup_nil hdepth with ⟨D, _⟩
  rcases D.cover_verts 0 (by simp) with ⟨i, _⟩
  exact Fin.elim0 i
