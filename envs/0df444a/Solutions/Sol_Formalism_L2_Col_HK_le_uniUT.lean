-- Prove2me | solution 1 for Formalism.L2.Col.HK_le_uniUT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:08.30133+00:00
-- url     : https://prove2.me/submissions/666d5a96-c7c2-411d-9670-d56279990b6c

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
theorem _root_.solution (n : ℕ) (κ : Type) [CommRing κ] (r : ℕ) (bl : List ℕ) : HK n κ r bl ≤ uniUT n κ r bl := by
  intro M h
  obtain ⟨h1, h2⟩ := mem_HK.mp h
  refine mem_uniUT.mpr ⟨h1, fun i j hi hji => ?_, fun i hi => ?_⟩
  · rw [h2 i j hi (by omega)]
    exact Matrix.one_apply_ne fun e => by rw [e] at hji; omega
  · rw [h2 i i hi hi, Matrix.one_apply_eq]
end Formalism.L2.Col
