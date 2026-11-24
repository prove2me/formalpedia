-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_InZ_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:05.800092+00:00
-- url     : https://prove2.me/submissions/8dfb332b-9db3-4750-a598-130f545ef69c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_map
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
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) {ι : Type} (P : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν) (x : MvPolynomial (Fin n × Fin n) ℚ)
    (hx : x ∈ Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i))) : qn_InZ n ν x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨_, h1 i, qn_T_map n (P i)⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Y1, h1, e1⟩ := hx
    obtain ⟨Y2, h2, e2⟩ := hy
    exact ⟨Y1 + Y2, Submodule.add_mem _ h1 h2, by rw [map_add, map_add, e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨Y1, h1, e1⟩ := hx
    exact ⟨c • Y1, Submodule.smul_mem _ _ h1, by rw [map_zsmul, map_zsmul, e1]⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
