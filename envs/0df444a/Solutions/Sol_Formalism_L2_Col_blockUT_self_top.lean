-- Prove2me | solution 1 for Formalism.L2.Col.blockUT_self_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:09:53.445931+00:00
-- url     : https://prove2.me/submissions/223b1e1c-438a-4117-b20a-29ecf731dc72

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
variable {n : ℕ} {κ : Type} [CommRing κ]
namespace Formalism.L2.Col
theorem _root_.solution (r : ℕ) : blockUT r κ r [] = ⊤ := by
  rw [eq_top_iff]
  intro M _
  show (M : Matrix (Fin r) (Fin r) κ).BlockTriangular (fun i => coarse r [] i.val)
  intro i j hij
  exfalso
  simp only [coarse, blkIdx, if_pos i.2, if_pos j.2] at hij
  exact lt_irrefl _ hij
end Formalism.L2.Col
