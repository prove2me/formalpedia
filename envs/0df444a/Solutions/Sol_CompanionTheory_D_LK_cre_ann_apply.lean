-- Prove2me | solution 1 for CompanionTheory.D.LK.cre_ann_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:45.963288+00:00
-- url     : https://prove2.me/submissions/2fc31093-562a-440a-9991-2911a61e496b

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreAnnApply
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_cre_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_sg_erase
import Theorems.Thm_CompanionTheory_D_LK_Car_sg_mul_self
import Theorems.Thm_CompanionTheory_D_LK_Car_tw_self
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_euler_filt
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_homotopy_ring
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_mem_filt_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open GlobalTheory.CompanionTheory.DSICKoszul (homotopy_ring filt mem_filt_succ euler_filt)
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {Z : Type} [AddCommGroup Z] [Module ℂ Z]
namespace CompanionTheory.D.LK
theorem _root_.solution (i : Pos n) (x : Cn n Z) (A : Finset (Pos n)) :
    cre i (ann i x) A = if i ∈ A then x A else 0 := by
  by_cases h : i ∈ A
  · simp [cre_apply, ann_apply, h, sg_erase i h, tw_self, smul_smul, sg_mul_self, insert_erase h]
  · simp [cre_apply, h]
end CompanionTheory.D.LK
