-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:55.368328+00:00
-- url     : https://prove2.me/submissions/da5227a7-05ca-43f0-a4c3-c9ea008e0637

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {K' : Type*} [CommRing K'] (f : K →+* K') (hZ : InPat lv k Z) : InPat lv k (Z.map f) := by
  intro i j h
  simp [Matrix.map_apply, hZ i j h]
end Formalism.L2.SG.Pf.Unip
