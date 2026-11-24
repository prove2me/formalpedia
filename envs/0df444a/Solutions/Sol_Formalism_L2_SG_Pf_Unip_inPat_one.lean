-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:44.333797+00:00
-- url     : https://prove2.me/submissions/0505027b-3ca6-4dd4-a360-f90593178ac1

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
theorem _root_.solution : InPat lv 0 (1 : Matrix ι ι K) := by
  intro i j h
  have hij : i ≠ j := by
    rintro rfl
    omega
  exact Matrix.one_apply_ne hij
end Formalism.L2.SG.Pf.Unip
