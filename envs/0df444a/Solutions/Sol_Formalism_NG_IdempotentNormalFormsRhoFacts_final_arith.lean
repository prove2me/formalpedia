-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.final_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:52.10554+00:00
-- url     : https://prove2.me/submissions/53822800-e306-423e-a728-13dd3e9afc16

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange

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
open Formalism.NG.IdempotentNormalFormsRhoFacts
namespace Formalism.NG.IdempotentNormalFormsRhoFacts
theorem _root_.solution (R X Y Z s k : ℕ∞) (c N vδ : ℕ∞) (hk : k ≤ X + c * N * vδ)
    (hm : Y ≤ N * (2 * vδ)) (hs : Z ≤ s + R) :
    k + Y + Z ≤ R + X + s + 4 * N * (c + 1) * vδ := by
  calc k + Y + Z ≤ (X + c * N * vδ) + N * (2 * vδ) + (s + R) := add_le_add (add_le_add hk hm) hs
    _ ≤ (X + c * N * vδ) + N * (2 * vδ) + (s + R) + (3 * c * N * vδ + 2 * N * vδ) := le_self_add
    _ = R + X + s + 4 * N * (c + 1) * vδ := by ring
end Formalism.NG.IdempotentNormalFormsRhoFacts
