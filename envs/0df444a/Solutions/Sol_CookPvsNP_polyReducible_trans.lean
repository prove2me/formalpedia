-- Prove2me | solution 1 for CookPvsNP.polyReducible_trans
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T10:20:29.608883+00:00
-- url     : https://prove2.me/submissions/90543bc3-4721-4e49-9c26-bf5df8ad2503
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

open CookPvsNP

theorem solution {Sym₁ Sym₂ Sym₃ : Type} {L₁ : Lang Sym₁} {L₂ : Lang Sym₂} {L₃ : Lang Sym₃}
    (h₁₂ : PolyReducible L₁ L₂) (h₂₃ : PolyReducible L₂ L₃) : PolyReducible L₁ L₃ := by
  rcases h₁₂ with ⟨f, hf, hfm⟩
  rcases h₂₃ with ⟨g, hg, hgm⟩
  refine ⟨g ∘ f, polyTimeComputable_comp f g hf hg, ?_⟩
  intro x
  exact Iff.trans (hfm x) (hgm (f x))
