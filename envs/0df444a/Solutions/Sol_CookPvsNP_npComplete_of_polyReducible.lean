-- Prove2me | solution 1 for CookPvsNP.npComplete_of_polyReducible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:55:48.879188+00:00
-- url     : https://prove2.me/submissions/2e7713af-f970-497d-b15d-43992a02e10f

import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_polyReducible_trans

open CookPvsNP

theorem solution {Sym₁ Sym₂ : Type} [Fintype Sym₁] [Fintype Sym₂]
    (L₁ : Lang Sym₁) (L₂ : Lang Sym₂) (h₁ : NPComplete L₁) (h₂ : L₂ ∈ NP Sym₂)
    (h : PolyReducible L₁ L₂) : NPComplete L₂ :=
  ⟨h₂, fun Sym' _ _ L' hL' => polyReducible_trans (h₁.2 Sym' L' hL') h⟩
