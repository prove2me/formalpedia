-- Prove2me | solution 1 for Formalism.L2.Col.blkDet_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:30.625797+00:00
-- url     : https://prove2.me/submissions/ee274457-4dd0-40db-b31f-37567365e8c9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ]
namespace Formalism.L2.Col
theorem _root_.solution {β : ℕ → ℕ} (c : ℕ) (M : ↥(btG n κ β)) :
    ((blkDet n κ β c M : κˣ) : κ) = ((M.1 : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => β i.val) c).det := rfl
end Formalism.L2.Col
