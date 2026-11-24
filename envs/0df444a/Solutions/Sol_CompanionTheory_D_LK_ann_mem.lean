-- Prove2me | solution 1 for CompanionTheory.D.LK.ann_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:37:45.04939+00:00
-- url     : https://prove2.me/submissions/82c49196-072e-41da-b671-1a37bb667e85

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreAnnApply
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_apply
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
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open GlobalTheory.CompanionTheory.DSICKoszul (homotopy_ring filt mem_filt_succ euler_filt)
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {Z : Type} [AddCommGroup Z] [Module ℂ Z]
namespace CompanionTheory.D.LK
theorem _root_.solution {Q : Submodule ℂ Z} {x : Cn n Z} (h : ∀ A, x A ∈ Q) (i : Pos n) (A : Finset (Pos n)) :
    ann i x A ∈ Q := by
  rw [ann_apply]; split_ifs
  · exact Q.zero_mem
  · exact Q.smul_mem _ (h _)
end CompanionTheory.D.LK
