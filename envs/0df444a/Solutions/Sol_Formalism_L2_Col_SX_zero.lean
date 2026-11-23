-- Prove2me | solution 1 for Formalism.L2.Col.SX_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:39.630865+00:00
-- url     : https://prove2.me/submissions/cf925adb-a22b-4186-a4d2-21c74251a6aa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

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
theorem _root_.solution (k m : ℕ) : SX k m 0 = Finset.range (k - 1) := by
  unfold SX
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, add_zero]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, Or.inl (by omega)⟩
end Formalism.L2.Col
