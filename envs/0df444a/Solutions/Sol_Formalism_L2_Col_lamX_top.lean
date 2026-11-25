-- Prove2me | solution 1 for Formalism.L2.Col.lamX_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:23:56.237336+00:00
-- url     : https://prove2.me/submissions/f763b80b-abb2-4a6c-b925-5866571bc5e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_SX_top

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
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n k t j : ℕ) : lamX ψ χ n k (j + 1) t j = lamJ ψ χ n (k + j) t j := by
  unfold lamX lamJ
  rw [SX_top]
end Formalism.L2.Col
