-- Prove2me | solution 1 for DeletionCode.WordPaths.subword_position_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:19.771875+00:00
-- url     : https://prove2.me/submissions/65b7e670-8b05-49d5-8340-23a036c10882

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_WordPaths

set_option autoImplicit true
open DeletionCode DeletionCode.WordPaths
open Windows
namespace DeletionCode.WordPaths
theorem _root_.solution
    (x p : Letters) (n k m a b : ℕ)
    (hx : KUnique x n k) (hkm : k ≤ m)
    (ha : a + m ≤ n) (hb : b + m ≤ n)
    (hleft : Agree x a p 0 m) (hright : Agree x b p 0 m) :
    a = b := by
  apply hx a b (by omega) (by omega)
  intro i hi
  exact (hleft i (by omega)).trans (hright i (by omega)).symm
end DeletionCode.WordPaths
