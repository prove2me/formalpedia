-- Prove2me | solution 1 for CompanionTheory.D.LK.pderiv_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:40.196819+00:00
-- url     : https://prove2.me/submissions/33d2a902-f483-4b18-926e-186bb4e5438c

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MvPolynomial
open scoped TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL GlobalTheory.CompanionTheory.DSVerma GlobalTheory.CompanionTheory.DSCover
open CompanionTheory.D.DSIC (KRel NC)
namespace CompanionTheory.D.LK
theorem _root_.solution {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (h : f.totalDegree ≤ 0) : pderiv i f = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 h), pderiv_C]
end CompanionTheory.D.LK
