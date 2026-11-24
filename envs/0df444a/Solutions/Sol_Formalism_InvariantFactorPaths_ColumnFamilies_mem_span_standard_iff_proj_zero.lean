-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.mem_span_standard_iff_proj_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:41.392983+00:00
-- url     : https://prove2.me/submissions/c559eada-d703-48da-b33c-b3986e4434bd

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_ev_zero_of_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_exists_coeff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_supp_in


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
    (F : Type) [Field F] (x : M.ι → F) :
    x ∈ Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ y = fun i => (CF.vec j I i : F)} ↔
      ∀ mu, Dominant mu → mu ∉ pi → qb_ev M F mu x = 0 := by
  constructor
  · intro hx mu hmu hout
    have : Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧
        y = fun i => (CF.vec j I i : F)} ≤ LinearMap.ker (qb_evL M F mu) := by
      rw [Submodule.span_le]
      rintro y ⟨j, hj, I, -, rfl⟩
      exact qb_ev_zero_of_mem CF F hpi hj I hmu hout
    exact this hx
  · intro h
    obtain ⟨a, rfl⟩ := qb_exists_coeff hA CF F x
    have hs := qb_supp_in hA CF F a pi hpi h
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : a y = 0
    · rw [hy, zero_smul]; exact zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y.1, hs y hy, y.2.1, y.2.2, rfl⟩)
end Formalism.InvariantFactorPaths.ColumnFamilies
