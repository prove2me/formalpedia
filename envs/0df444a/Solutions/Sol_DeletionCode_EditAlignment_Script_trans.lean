-- Prove2me | solution 1 for DeletionCode.EditAlignment.Script.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:01:43.143622+00:00
-- url     : https://prove2.me/submissions/bccc575f-f52f-43ea-be96-38362e3204be

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
namespace Script
theorem _root_.solution {x y z : Word} {d₁ i₁ d₂ i₂ : ℕ}
    (hxy : Script x y d₁ i₁) (hyz : Script y z d₂ i₂) :
    Script x z (d₁ + d₂) (i₁ + i₂) := by
  induction hyz with
  | refl => simpa using hxy
  | delete h ih => simpa only [Nat.add_assoc] using Script.delete ih
  | insert h ih => simpa only [Nat.add_assoc] using Script.insert ih
end Script
end DeletionCode.EditAlignment
