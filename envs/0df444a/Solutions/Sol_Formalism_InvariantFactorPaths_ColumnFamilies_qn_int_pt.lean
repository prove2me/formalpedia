-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_int_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:15.254636+00:00
-- url     : https://prove2.me/submissions/7f7f902b-2d74-4be1-bac6-7a2ba8acd6b0

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_pt_step
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_pt_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_X_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z) (D : Finset (Fin n × Fin n)) :
    (∀ x ∈ D, x.2 < x.1) → ∀ F ∈ W, aeval (qn_pt n D) F ∈ qn_IntS n := by
  classical
  induction D using Finset.induction_on_min_value (fun x : Fin n × Fin n => x.1) with
  | empty =>
    intro _ F hF
    obtain ⟨z, hz⟩ := hev F hF
    rw [qn_pt_empty, hz]
    exact ⟨C z, by simp⟩
  | insert w D hw hmin ih =>
    obtain ⟨a, s⟩ := w
    intro hD F hF
    have hsa : s < a := hD (a, s) (Finset.mem_insert_self _ _)
    have hs : ∀ c, (s, c) ∉ D := by
      intro c hc
      have := hmin (s, c) hc
      exact absurd hsa (not_lt.mpr this)
    have ih' := ih (fun x hx => hD x (Finset.mem_insert_of_mem hx))
    rw [qn_pt_step n D a s hw hs, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Subring.mul_mem _ (ih' _ (hW F hF s a k (ne_of_lt hsa))) (Subring.pow_mem _ (qn_X_mem n _) _)
end Formalism.InvariantFactorPaths.ColumnFamilies
