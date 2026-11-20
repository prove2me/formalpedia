-- Prove2me | solution 1 for DeletionCode.EditAlignment.Script.classify_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:46.379757+00:00
-- url     : https://prove2.me/submissions/bd6cfa69-894e-4cf8-9df2-44c6367147ed

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
import Theorems.Thm_DeletionCode_EditAlignment_Script_zero_eq

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
namespace Script
theorem _root_.solution {x y : Word} {d i : ℕ}
    (h : Script x y d i) (hcost : d + i ≤ 1) :
    x = y ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ bit :: suffix ∧ y = pre ++ suffix) ∨
      (∃ (pre suffix : Word) (bit : Bool),
        x = pre ++ suffix ∧ y = pre ++ bit :: suffix) := by
  cases h with
  | refl => exact Or.inl rfl
  | @delete pre suffix bit d i h =>
    have hd : d = 0 := by omega
    have hi : i = 0 := by omega
    subst d
    subst i
    exact Or.inr (Or.inl ⟨pre, suffix, bit, h.zero_eq, rfl⟩)
  | @insert pre suffix bit d i h =>
    have hd : d = 0 := by omega
    have hi : i = 0 := by omega
    subst d
    subst i
    exact Or.inr (Or.inr ⟨pre, suffix, bit, h.zero_eq, rfl⟩)
end Script
end DeletionCode.EditAlignment
