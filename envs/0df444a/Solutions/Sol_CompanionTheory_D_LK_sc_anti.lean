-- Prove2me | solution 1 for CompanionTheory.D.LK.sc_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:24.364804+00:00
-- url     : https://prove2.me/submissions/4bcb406a-26c9-4df3-bd06-030f7de2a34d

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
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
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq term_le normSq_le pair_lt abs_sig rho_eq)
open PI.UpqRep
variable {n : ℕ}
namespace CompanionTheory.D.LK
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) : sc ε b a = -sc ε a b := by
  unfold sc
  by_cases h : ε a = ε b
  · rw [if_pos h, if_pos h.symm, sig_anti]
  · rw [if_neg h, if_neg (Ne.symm h), neg_zero]
end CompanionTheory.D.LK
