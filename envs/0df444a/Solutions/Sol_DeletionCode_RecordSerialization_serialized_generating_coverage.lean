-- Prove2me | solution 1 for DeletionCode.RecordSerialization.serialized_generating_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:05:18.925387+00:00
-- url     : https://prove2.me/submissions/e6422655-af89-40e7-bc46-d175f3fd253f

import Definitions.Def_DeletionCode_RecordBounds
import Definitions.Def_DeletionCode_RecordPacking
import Definitions.Def_DeletionCode_RecordSerialization
import Theorems.Thm_DeletionCode_RecordSerialization_description_roundtrip
import Theorems.Thm_DeletionCode_RecordBounds_generating_decode_exists_bounded


set_option autoImplicit true
open DeletionCode DeletionCode.RecordSerialization
open Windows HeaderRecovery ConcreteDecoder DescriptionCount RecordCodec
open RecordPacking GeneratingModel
namespace DeletionCode.RecordSerialization
theorem _root_.solution {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (x : Letters) (n c : ℕ) (hν : 1 ≤ ν) (hx : KUnique x n k)
    (hg : E.family.Generating x n (windowLength k))
    (hc : Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) = c) :
    ∃ description : Description n (windowLength k) ν c,
      decodeDescription x n k ν c hν description = some (dataOfFamily E) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode, hpos, hbounded⟩ :=
    RecordBounds.generating_decode_exists_bounded E x n hx hg
  have hhi : ∀ b, (E.header b).rho ≤ windowLength k := by
    intro b
    have := E.rho_upper b
    unfold windowLength
    omega
  have hrootc : roots.length = c := hroots.trans hc
  let description := encodeDescription n k ν c hν E.header E.rho_lower hhi
    roots hrootc hpos instructions
  refine ⟨description, ?_⟩
  rw [description_roundtrip x n k ν c hν E.header E.rho_lower hhi roots hrootc hpos
    instructions (by simpa using hcost) hbounded, hdecode]
  rfl
end DeletionCode.RecordSerialization
