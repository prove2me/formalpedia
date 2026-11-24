-- Prove2me | solution 1 for Formalism.NG.TrivialCharacterBlockLength.final_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:39.846316+00:00
-- url     : https://prove2.me/submissions/f68586ea-5f05-4efd-91ca-c5e186e78a76

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.TrivialCharacterBlockLength
namespace Formalism.NG.TrivialCharacterBlockLength
theorem _root_.solution (k X c vδ s R1 R2 : ℕ∞) (hk : k ≤ X + c * vδ) :
    k + (s + (R1 + R2)) ≤ s + X + R1 + 4 * (c + 1) * vδ + R2 := by
  calc k + (s + (R1 + R2)) ≤ (X + c * vδ) + (s + (R1 + R2)) := add_le_add hk le_rfl
    _ ≤ (X + c * vδ) + (s + (R1 + R2)) + (3 * c * vδ + 4 * vδ) := le_self_add
    _ = s + X + R1 + 4 * (c + 1) * vδ + R2 := by ring
end Formalism.NG.TrivialCharacterBlockLength
