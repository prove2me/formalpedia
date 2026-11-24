-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_mem_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:42.179447+00:00
-- url     : https://prove2.me/submissions/dafc328b-097b-4779-9aaf-6afd79fddea7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_exists_coeff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_supp_in
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_vecF_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi)
    (x : M.ι → ℤ) (h : ∀ mu, Dominant mu → mu ∉ pi → qb_ev M ℚ mu (fun i => (x i : ℚ)) = 0) :
    x ∈ Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} := by
  obtain ⟨a, rfl⟩ := qb_exists_coeff hA CF ℤ x
  have hc : (fun i => (((∑ y, a y • qb_vecF CF ℤ y) i : ℤ) : ℚ)) = ∑ y, (a y : ℚ) • qb_vecF CF ℚ y := by
    funext i
    simp [qb_vecF, Finset.sum_apply]
  rw [hc] at h
  have hs := qb_supp_in hA CF ℚ (fun y => (a y : ℚ)) pi hpi h
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hy : a y = 0
  · rw [hy, zero_smul]; exact zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨y.1, hs y (by exact_mod_cast hy), y.2.1, y.2.2, by rw [qb_vecF_int]⟩)
end Formalism.InvariantFactorPaths.ColumnFamilies
