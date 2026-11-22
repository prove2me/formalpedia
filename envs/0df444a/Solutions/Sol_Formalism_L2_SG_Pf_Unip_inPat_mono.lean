-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:46.39928+00:00
-- url     : https://prove2.me/submissions/1a04b7b9-34bb-4294-81b5-84dea211493c

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
theorem _root_.solution (hkl : k ≤ l) (hZ : InPat lv l Z) : InPat lv k Z := fun i j h => hZ i j (by omega)
end Formalism.L2.SG.Pf.Unip
