-- Prove2me | solution 1 for CompanionTheory.D.LK.ind_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:24.390189+00:00
-- url     : https://prove2.me/submissions/07306827-aca2-477c-ae47-42006244d5c3

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
theorem _root_.solution (A : Finset (Pos n)) (a b : Fin n) :
    ind A a b = if h : a < b then (if (⟨(a, b), h⟩ : Pos n) ∈ A then 1 else 0) else 0 := by
  unfold ind
  split_ifs with h h1
  · rw [Finset.sum_eq_single_of_mem _ h1 fun i _ hi => if_neg fun e => hi (Subtype.ext e), if_pos rfl]
  · exact Finset.sum_eq_zero fun i hi => if_neg fun e => h1 ((Subtype.ext e : i = ⟨(a, b), h⟩) ▸ hi)
  · exact Finset.sum_eq_zero fun i _ => if_neg fun e => h (by have := i.2; rwa [e] at this)
end CompanionTheory.D.LK
