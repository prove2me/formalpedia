-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.det_mem_dual_weyl_ones
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:28.804933+00:00
-- url     : https://prove2.me/submissions/23916bc0-f9a1-4829-a97f-36a69efc0bd9

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (r : ℕ) : genericDet ℤ r ∈ dualWeyl ℤ r r (fun _ => 1) := by
  unfold dualWeyl
  rw [Submodule.mem_inf]
  constructor
  · unfold genericDet
    rw [Matrix.det_apply]
    refine Submodule.sum_mem _ (fun σ _ => ?_)
    rw [Units.smul_def]
    refine Submodule.smul_mem _ _ ?_
    rw [mem_weightedHomogeneousSubmodule]
    have hp := IsWeightedHomogeneous.prod (w := colW r r) Finset.univ
      (fun i => genericMatrix' ℤ r (σ i) i) (fun i => colW r r (σ i, i))
      (fun i _ => by simpa [genericMatrix'] using isWeightedHomogeneous_X (R := ℤ) (w := colW r r) (σ i, i))
    convert hp using 1
    funext t
    simp [colW, Finset.sum_apply, Pi.single_apply]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero]
    intro l j hlj
    have hM : (colAddGen ℤ l j).mapMatrix (genericMatrix' ℤ r) =
        Matrix.transpose ((Matrix.transpose ((rename (R := ℤ)
          (some : Fin r × Fin r → Option (Fin r × Fin r))).mapMatrix (genericMatrix' ℤ r))).updateRow j
          (Matrix.transpose ((rename (R := ℤ)
            (some : Fin r × Fin r → Option (Fin r × Fin r))).mapMatrix (genericMatrix' ℤ r)) j +
          (X none : MvPolynomial (Option (Fin r × Fin r)) ℤ) •
            Matrix.transpose ((rename (R := ℤ)
              (some : Fin r × Fin r → Option (Fin r × Fin r))).mapMatrix (genericMatrix' ℤ r)) l)) := by
      ext p q
      by_cases hq : q = j
      · subst hq
        simp [colAddGen, genericMatrix', Matrix.updateRow_apply]
      · simp [colAddGen, genericMatrix', Matrix.updateRow_apply, hq]
    unfold genericDet
    rw [AlgHom.map_det (colAddGen ℤ l j), hM, Matrix.det_transpose,
      Matrix.det_updateRow_add_smul_self _ hlj.ne', Matrix.det_transpose, ← AlgHom.map_det]
end Formalism.CohomologicalDescent.LA
