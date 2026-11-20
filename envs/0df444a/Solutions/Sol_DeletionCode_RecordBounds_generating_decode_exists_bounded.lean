-- Prove2me | solution 1 for DeletionCode.RecordBounds.generating_decode_exists_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:04:32.463179+00:00
-- url     : https://prove2.me/submissions/f661a46c-1450-447b-abda-875df083e38f

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
import Theorems.Thm_DeletionCode_RecordBounds_decode_bounded
import Theorems.Thm_DeletionCode_GeneratingRecovery_generating_decode_exists


set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.RecordBounds
theorem _root_.solution [Fintype B]
    (E : GeneratingModel.EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ∃ roots instructions,
      roots.length = Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k E.header roots instructions =
        some (fun b i => negativePath k (E.header b) (E.long b) i.val) ∧
      (∀ b a, (b, a) ∈ roots → a < n) ∧
      (∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction) := by
  obtain ⟨roots, instructions, hroots, hcost, hdecode⟩ :=
    GeneratingRecovery.generating_decode_exists E x n hx hg
  have hbounds := decode_bounded x n k E.header E.rho_lower E.rho_upper roots instructions _ hdecode
  exact ⟨roots, instructions, hroots, hcost, hdecode, hbounds⟩
end DeletionCode.RecordBounds
