-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_atP_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:18.946617+00:00
-- url     : https://prove2.me/submissions/f0531c05-fcb6-42fc-903e-9d662c06e70f

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
theorem _root_.solution (v : Pl) (f : MvPowerSeries (ι v) K) (n : (Σ v, ι v) →₀ ℕ)
    (h : ∀ m, n ≠ eqv.symm (Pi.single v m)) : MvPowerSeries.coeff n (atP v f) = 0 := by
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨u, hu⟩
  refine h u ?_
  rw [← hu, eq_comm, AddEquiv.symm_apply_eq, ← eqv_embDomain v u]
  exact congrArg eqv (Finsupp.embDomain_eq_mapDomain (Function.Embedding.sigmaMk v) u)
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
