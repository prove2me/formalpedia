-- Prove2me | solution 1 for DeletionCode.RecordSerialization.roots_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:02:15.399838+00:00
-- url     : https://prove2.me/submissions/b80d1c07-cb7c-460e-bcd9-9dd7fbeb424b

import Definitions.Def_DeletionCode_RecordBounds
import Definitions.Def_DeletionCode_RecordPacking
import Definitions.Def_DeletionCode_RecordSerialization

set_option autoImplicit true
open DeletionCode DeletionCode.RecordSerialization
open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel
namespace DeletionCode.RecordSerialization
theorem _root_.solution (n ν c : ℕ) (roots : List (Fin ν × ℕ))
    (hlen : roots.length = c) (hpos : ∀ b a, (b, a) ∈ roots → a < n) :
    rootsOfVectors (rootVectors n ν c roots hlen hpos).1
      (rootVectors n ν c roots hlen hpos).2 = roots := by
  subst c
  change List.ofFn (fun i : Fin roots.length => roots.get i) = roots
  simp
end DeletionCode.RecordSerialization
