-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.eqv_embDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:37.154845+00:00
-- url     : https://prove2.me/submissions/b38aa085-020f-4d34-868d-25004afa6148

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename

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
theorem _root_.solution (v : Pl) (m : ι v →₀ ℕ) :
    eqv (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) = Pi.single v m := by
  funext w
  ext i
  rw [Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
  by_cases h : w = v
  · subst h
    rw [Pi.single_eq_same]
    exact Finsupp.embDomain_apply_self (Function.Embedding.sigmaMk w) m i
  · rw [Pi.single_eq_of_ne h, Finsupp.coe_zero, Pi.zero_apply, Finsupp.embDomain_notin_range]
    rintro ⟨j, hj⟩
    exact h (congrArg Sigma.fst hj).symm
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
