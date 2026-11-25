-- Prove2me | solution 1 for Formalism.L2.Col.lamKJ_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:07:26.086522+00:00
-- url     : https://prove2.me/submissions/b0bf96d9-c1ff-4afe-b840-41ea205a25a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_lamK_ne_one
import Theorems.Thm_Formalism_L2_Col_coarse_replicate

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
theorem _root_.solution (χ : ℕ → κˣ →* Kˣ) {r t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : r + j * t ≤ n) (hχ : χ s ≠ 1) :
    lamKJ χ n r t j ≠ 1 := by
  unfold lamKJ
  have hst : s * t < j * t := Nat.mul_lt_mul_of_pos_right hs ht
  exact lamK_ne_one χ (List.replicate j t) (⟨r + s * t, by omega⟩ : Fin n) (by simpa using hs) (coarse_replicate ht hs) hχ
end Formalism.L2.Col
