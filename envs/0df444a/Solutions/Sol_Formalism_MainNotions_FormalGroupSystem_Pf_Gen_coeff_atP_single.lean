-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_atP_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:19.191807+00:00
-- url     : https://prove2.me/submissions/4a7dbf87-dfd6-4f58-b28f-372705e4aed0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_eqv_embDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
variable [Fintype Pl]
variable [DecidableEq Pl]
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution (v : Pl) (f : MvPowerSeries (ι v) K) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff (eqv.symm (Pi.single v m)) (atP v f) = MvPowerSeries.coeff m f := by
  have h : eqv.symm (Pi.single v m) = Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
    rw [AddEquiv.symm_apply_eq, eqv_embDomain]
  rw [h]
  exact MvPowerSeries.coeff_embDomain_rename _ _ _
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
