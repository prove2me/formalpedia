-- Prove2me | solution 1 for CompanionTheory.D.LK.deg_X_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:58.183674+00:00
-- url     : https://prove2.me/submissions/c0c008be-cdaf-4468-90e6-b5359fc89498

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial
import Theorems.Thm_CompanionTheory_D_LK_deg_pderiv
import Theorems.Thm_CompanionTheory_D_LK_pderiv_deg_zero
import Theorems.Thm_CompanionTheory_D_LK_deg_X_mul
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset MvPolynomial
open scoped TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL GlobalTheory.CompanionTheory.DSVerma GlobalTheory.CompanionTheory.DSCover
open CompanionTheory.D.DSIC (KRel NC)
namespace CompanionTheory.D.LK
theorem _root_.solution {σ : Type} (j i : σ) (f : MvPolynomial σ ℂ) : (X j * pderiv i f).totalDegree ≤ f.totalDegree := by
  cases h : f.totalDegree with
  | zero => simp [pderiv_deg_zero i f h.le]
  | succ k => exact (deg_X_mul _ _).trans (Nat.succ_le_succ (deg_pderiv i f k h.le))
end CompanionTheory.D.LK
