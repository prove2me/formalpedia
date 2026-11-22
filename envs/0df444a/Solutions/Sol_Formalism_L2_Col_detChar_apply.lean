-- Prove2me | solution 1 for Formalism.L2.Col.detChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:15.700937+00:00
-- url     : https://prove2.me/submissions/1258649d-82cc-4e25-8a5f-7a04b4890cd4

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
theorem _root_.solution (χ : ℕ → κˣ →* Kˣ) (a : ℕ) (bl : List ℕ) (M : ↥(blockUT n κ a bl)) :
    detChar χ n a bl M = ∏ s ∈ Finset.range bl.length, χ s (blkDet n κ (coarse a bl) (s + 1) M) := by
  rw [detChar, MonoidHom.finsetProd_apply]; rfl
end Formalism.L2.Col
