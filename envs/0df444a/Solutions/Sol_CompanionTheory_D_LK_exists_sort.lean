-- Prove2me | solution 1 for CompanionTheory.D.LK.exists_sort
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:24.215022+00:00
-- url     : https://prove2.me/submissions/16d5f681-5938-4516-93be-e364856f6874

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
theorem _root_.solution (ε : Fin n → Bool) (κ : Fin n → ℝ) : ∃ w : Equiv.Perm (Fin n), (∀ c, ε (w c) = ε c) ∧
    ∀ a b, a < b → ε a = ε b → κ (w b) ≤ κ (w a) := by
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image (univ.filter fun w : Equiv.Perm (Fin n) => ∀ c, ε (w c) = ε c)
    (fun w => ∑ c, κ (w c) * ((c : ℕ) : ℝ)) ⟨1, by simp⟩
  have hw' := (mem_filter.1 hw).2
  refine ⟨w, hw', fun a b hab h => ?_⟩
  have := hmin (w * Equiv.swap a b) (mem_filter.2 ⟨mem_univ _, fun c => by
    rw [Equiv.Perm.mul_apply, hw', Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl⟩)
  have e : ∑ c, κ ((w * Equiv.swap a b) c) * ((c : ℕ) : ℝ) - ∑ c, κ (w c) * ((c : ℕ) : ℝ) =
      (κ (w a) - κ (w b)) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem a b (mem_univ _) (mem_univ _) hab.ne]
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]; ring
    · intro c _ hc
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2, sub_self]
  have hp : (0 : ℝ) < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := sub_pos.2 (by exact_mod_cast hab)
  have : 0 ≤ (κ (w a) - κ (w b)) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by rw [← e]; linarith
  linarith [nonneg_of_mul_nonneg_left this hp]
end CompanionTheory.D.LK
