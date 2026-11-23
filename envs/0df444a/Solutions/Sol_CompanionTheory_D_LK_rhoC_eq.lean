-- Prove2me | solution 1 for CompanionTheory.D.LK.rhoC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:24.428086+00:00
-- url     : https://prove2.me/submissions/f632f228-d11f-48e6-acaf-a39eadc76ea4

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_abs_sig
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_normSq_le
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_pair_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_rho_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_anti
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_term_le
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
open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq term_le normSq_le pair_lt abs_sig rho_eq)
open PI.UpqRep
variable {n : ℕ}
namespace CompanionTheory.D.LK
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) : rhoC ε a = (∑ b, sc ε a b) / 2 := by
  unfold rhoC
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold sc sig
  rcases lt_trichotomy a b with h | h | h
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2, eq_comm (a := ε a)]
  · simp [h]
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2, eq_comm (a := ε a)]
end CompanionTheory.D.LK
