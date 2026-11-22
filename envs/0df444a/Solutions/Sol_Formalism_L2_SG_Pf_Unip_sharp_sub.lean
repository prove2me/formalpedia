-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.sharp_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:50.026082+00:00
-- url     : https://prove2.me/submissions/a13862e8-091d-4714-872d-d347865cb788

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
theorem _root_.solution (M N : Matrix ι ι K) : sharp J J' (M - N) = sharp J J' M - sharp J J' N := by
  simp only [sharp, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
end Formalism.L2.SG.Pf.Unip
