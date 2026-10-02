-- Prove2me | solution 1 for CookPvsNP.comp_conversion_entry
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:42.398282+00:00
-- url     : https://prove2.me/submissions/d50673cb-470c-439c-aaa2-82e1c54aefa8

import Definitions.Def_CookPvsNP_CompConversion

set_option autoImplicit false
open CookPvsNP

/-- A halted first simulation installs the origin and left-boundary markers in two steps. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : Cfg A M₁.Q) (hn : M₁.IsHalting c) :
    (compTM j₁ j₂ M₁ M₂).run 2 (compFirstCfg c) =
      ⟨.convCopy true,
        CompCell.leftMarker (c.left.headD none) :: c.left.tail.map CompCell.firstSymbol,
        CompCell.originSymbol c.head none,
        c.right.map CompCell.firstSymbol ++ [CompCell.rightMarker]⟩ := by
  rcases c with ⟨q, left, head, right⟩
  change q = M₁.qaccept ∨ q = M₁.qreject at hn
  cases head <;> cases left with
  | nil =>
    simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
      compFirstCfg, CompCell.firstSymbol, CompCell.plain, CompCell.originSymbol,
      CompCell.leftMarker, CompCell.pack, CompCell.unpack, CompCell.blank, hn]
  | cons a left =>
    cases a <;> simp [TM.run, Function.iterate_succ_apply, TM.step, TM.IsHalting, compTM,
      compFirstCfg, CompCell.firstSymbol, CompCell.plain, CompCell.originSymbol,
      CompCell.leftMarker, CompCell.pack, CompCell.unpack, CompCell.blank, hn]

#print axioms solution
