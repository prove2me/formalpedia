-- Prove2me | solution 1 for CookPvsNP.polyTimeComputable_comp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T17:10:00.965578+00:00
-- url     : https://prove2.me/submissions/de1dedae-ce6d-4be8-bd57-d7739fe76441
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_CookPvsNP_tm_compose_poly_witness

set_option autoImplicit false

open CookPvsNP

theorem solution {Sym₁ Sym₂ Sym₃ : Type}
    (f : List Sym₁ → List Sym₂) (g : List Sym₂ → List Sym₃)
    (hf : CookPvsNP.PolyTimeComputable f) (hg : CookPvsNP.PolyTimeComputable g) :
    CookPvsNP.PolyTimeComputable (g ∘ f) := by
  rcases hf with ⟨Γ₁, hfin₁, ι₁, ι₂₁, M₁, k₁, h₁⟩
  rcases hg with ⟨Γ₂, hfin₂, ι₂₂, ι₃, M₂, k₂, h₂⟩
  letI : Fintype Γ₁ := hfin₁
  letI : Fintype Γ₂ := hfin₂
  exact CookPvsNP.tm_compose_poly_witness ι₁ ι₂₁ M₁ k₁ ι₂₂ ι₃ M₂ k₂ f g h₁ h₂