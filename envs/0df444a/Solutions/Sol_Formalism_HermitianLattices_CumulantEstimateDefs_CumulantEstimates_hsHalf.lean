-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.hsHalf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:44.468108+00:00
-- url     : https://prove2.me/submissions/314a21b9-53ae-42b4-af66-5bc4dee86603

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
open scoped ComplexOrder
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : Formalism.HermitianLattices.CumulantEstimateDefs.HilbertSchmidtHalfBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.HilbertSchmidtHalfBound
  intro d A hA
  have hdiag : ∀ i, (1:ℝ) / 4 ≤ ‖A i i‖ ^ 2 := by
    intro i
    have h0 := (Complex.le_def.1 (hA.diag_nonneg (i := i))).1
    simp [Matrix.sub_apply, Matrix.one_apply] at h0
    have hn := Complex.re_le_norm (A i i)
    have h1 : 1 / 2 ≤ ‖A i i‖ := by linarith
    nlinarith [h1]
  calc (d : ℝ) / 4 = ∑ _i : Fin d, (1:ℝ) / 4 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ∑ i, ‖A i i‖ ^ 2 := Finset.sum_le_sum fun i _ => hdiag i
    _ ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
