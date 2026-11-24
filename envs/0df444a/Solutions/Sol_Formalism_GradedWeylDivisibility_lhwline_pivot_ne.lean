-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_pivot_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:57.895971+00:00
-- url     : https://prove2.me/submissions/26b8b30a-dc96-4fff-92e5-137c61219d5f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (k : ℕ) (hr : k + 1 ≤ r) (hn : k + 1 ≤ n) (y : Fin r × Fin n → K)
    (hy : lhwline_cleared k y) (hd : eval y (lpMinor K (k + 1) hr hn) ≠ 0) :
    y (⟨k, hr⟩, ⟨k, hn⟩) ≠ 0 := by
  intro h0
  apply hd
  rw [lpMinor, RingHom.map_det]
  refine Matrix.det_eq_zero_of_column_eq_zero (Fin.last k) (fun i => ?_)
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X]
  by_cases hi : i = Fin.last k
  · subst hi
    have e1 : Fin.castLE hr (Fin.last k) = ⟨k, hr⟩ := Fin.ext (by simp)
    have e2 : Fin.castLE hn (Fin.last k) = ⟨k, hn⟩ := Fin.ext (by simp)
    rw [e1, e2]
    exact h0
  · have hik : i.val < k := Fin.val_lt_last hi
    exact hy _ _ (by rw [Fin.coe_castLE, Fin.coe_castLE, Fin.val_last]; omega)
      (Or.inl (by rw [Fin.coe_castLE]; exact hik))
end Formalism.GradedWeylDivisibility
