-- Prove2me | solution 1 for CompanionTheory.D.LK.wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:24.716989+00:00
-- url     : https://prove2.me/submissions/e12cff97-2840-4848-9113-ef8ae28ed6e9

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
theorem _root_.solution (A : Finset (Pos n)) (c : Fin n) : wt A c = ∑ b, (ind A c b - ind A b c) := by
  rw [Finset.sum_sub_distrib]
  unfold wt ind
  rw [Finset.sum_comm, Finset.sum_comm (s := univ), card_filter, card_filter, Nat.cast_sum, Nat.cast_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · simp only [Prod.ext_iff, ite_and]
    split_ifs <;> simp
  · simp only [Prod.ext_iff, ite_and, Finset.sum_ite_eq, mem_univ, if_true]
    split_ifs <;> simp
end CompanionTheory.D.LK
