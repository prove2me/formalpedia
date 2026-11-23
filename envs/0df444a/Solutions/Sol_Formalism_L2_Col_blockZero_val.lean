-- Prove2me | solution 1 for Formalism.L2.Col.blockZero_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:34.579947+00:00
-- url     : https://prove2.me/submissions/794db5d1-fc46-479b-884d-7bcbc745162e

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
variable {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution {r : ℕ} (h : r ≤ n) (bl : List ℕ) (M : ↥(blockUT n κ r bl)) :
    (blk0 n κ h bl M : Matrix (Fin r) (Fin r) κ) = restr h (M.1 : Matrix (Fin n) (Fin n) κ) := rfl
end Formalism.L2.Col
