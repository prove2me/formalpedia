-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.sharp_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:46.373591+00:00
-- url     : https://prove2.me/submissions/d9c39d98-5944-44f3-a1c6-fc80e0a609e7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
variable {lv : ι → ℕ} {T k : ℕ}
variable {J J' : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (h : J' * J = 1) : sharp J J' (1 : Matrix ι ι K) = 1 := by
  simp only [sharp, conjTranspose_one, Matrix.mul_one, h]
end Formalism.L2.SG.Pf.Unip
