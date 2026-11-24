-- Prove2me | solution 1 for Formalism.L2.Col.lamQ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:02.411091+00:00
-- url     : https://prove2.me/submissions/367f9ea6-5bb1-4dc8-aace-3452f08560d3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Theorems.Thm_Formalism_L2_Col_detChar_apply

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
variable (κ : Type) [CommRing κ] {K : Type} [Field K]
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
namespace Formalism.L2.Col
theorem _root_.solution (ξ : κˣ →* Kˣ) (n a b : ℕ) (M : ↥(HQ κ n a b)) :
    lamQ ξ n a b M = ξ (blkDet n κ (coarse a [b]) 1 M) := by
  rw [lamQ, detChar_apply]
  simp
end Formalism.L2.Col
