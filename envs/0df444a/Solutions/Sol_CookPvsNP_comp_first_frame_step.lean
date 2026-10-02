-- Prove2me | solution 1 for CookPvsNP.comp_first_frame_step
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T08:35:48.754983+00:00
-- url     : https://prove2.me/submissions/73fe278d-ebe1-4392-8a5f-a1331690d789

import Definitions.Def_CookPvsNP_CompFrames

set_option autoImplicit false

open CookPvsNP

private theorem unpack_first {Γ₁ Γ₂ : Type} (a : Option Γ₁) :
    CompCell.unpack (CompCell.firstSymbol (Γ₂ := Γ₂) a) =
      ⟨a, none, false, false, false, false, false⟩ := by
  cases a <;> simp [CompCell.firstSymbol, CompCell.plain, CompCell.pack,
    CompCell.unpack, CompCell.blank]

private theorem pack_first {Γ₁ Γ₂ : Type} (a : Option Γ₁) :
    CompCell.pack (⟨a, none, false, false, false, false, false⟩ : CompCell Γ₁ Γ₂) =
      CompCell.firstSymbol a := rfl

private theorem first_none {Γ₁ Γ₂ : Type} :
    CompCell.firstSymbol (Γ₁ := Γ₁) (Γ₂ := Γ₂) none = none := rfl

private theorem pack_right {Γ₁ Γ₂ : Type} :
    CompCell.pack (⟨none, none, false, false, true, false, false⟩ : CompCell Γ₁ Γ₂) =
      CompCell.rightMarker := rfl

private theorem unpack_right {Γ₁ Γ₂ : Type} :
    CompCell.unpack (CompCell.rightMarker : Option (CompCell Γ₁ Γ₂)) =
      ⟨none, none, false, false, true, false, false⟩ := rfl

private theorem unpack_none {Γ₁ Γ₂ : Type} :
    CompCell.unpack (none : Option (CompCell Γ₁ Γ₂)) =
      ⟨none, none, false, false, false, false, false⟩ := rfl

/-- The first simulation phase preserves its exact finite-list representation. -/
theorem solution {S Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (j₁ : S ↪ Γ₁) (j₂ : S ↪ Γ₂) (M₁ : TM Γ₁) (M₂ : TM Γ₂)
    (c : Cfg Γ₁ M₁.Q) (hn : ¬ M₁.IsHalting c) :
    (compTM j₁ j₂ M₁ M₂).run 3 (compFirstCfg c) = compFirstCfg (M₁.step c) := by
  classical
  rcases c with ⟨q, left, head, right⟩
  have hq : ¬ (q = M₁.qaccept ∨ q = M₁.qreject) := hn
  rcases hd : M₁.δ q head with ⟨q', w, move⟩
  cases move <;> cases left <;> cases right <;>
    simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
      compFirstCfg, unpack_first, pack_first, first_none, pack_right,
      unpack_right, unpack_none, hq, hd]

#print axioms solution
