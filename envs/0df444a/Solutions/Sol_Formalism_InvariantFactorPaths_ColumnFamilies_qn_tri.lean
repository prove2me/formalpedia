-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_tri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:44.775625+00:00
-- url     : https://prove2.me/submissions/1a24455d-73bd-40f1-803c-eabda50cb6a7

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_int_pt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_coeff_pt
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_weight_col


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z)
    (hcol : ∀ F ∈ W, IsWeightedHomogeneous (colW n n) F ν) :
    ∀ F ∈ W, ∀ e : Fin n × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e F = z := by
  classical
  intro F hF e he
  by_cases hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t
  · rw [← qn_coeff_pt n ν F (hcol F hF) e he hec]
    obtain ⟨G, hG⟩ := qn_int_pt n W hW hev (qn_low n) (fun x hx => (Finset.mem_filter.mp hx).2) F hF
    refine ⟨coeff (qn_off e) G, ?_⟩
    rw [← hG, coeff_map]
    rfl
  · refine ⟨0, ?_⟩
    rw [Int.cast_zero]
    by_contra hne
    apply hec
    intro t
    rw [← lhwline_weight_col, hcol F hF hne]
end Formalism.InvariantFactorPaths.ColumnFamilies
