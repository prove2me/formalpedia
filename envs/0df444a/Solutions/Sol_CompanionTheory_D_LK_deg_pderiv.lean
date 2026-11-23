-- Prove2me | solution 1 for CompanionTheory.D.LK.deg_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:39.601732+00:00
-- url     : https://prove2.me/submissions/bf6d5676-8724-4bb7-8331-9a8d63418b41

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial
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
theorem _root_.solution {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (k : ℕ) (h : f.totalDegree ≤ k + 1) :
    (pderiv i f).totalDegree ≤ k := by
  classical
  rw [f.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (totalDegree_monomial_le _ _).trans ?_
    have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      omega
    have e2 := congrArg Finsupp.degree e
    rw [map_add, Finsupp.degree_single] at e2
    have h3 := (le_totalDegree hs).trans h
    change s.degree ≤ k + 1 at h3
    change (s - Finsupp.single i 1).degree ≤ k
    omega
end CompanionTheory.D.LK
