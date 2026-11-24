-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.trace_restrict_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:15:01.782972+00:00
-- url     : https://prove2.me/submissions/9b9b08cc-f1b6-4728-adb1-dc32861520ca

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {ι n : Type} [Fintype ι] [Fintype n]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] [Module.Free ℂ M] [Module.Finite ℂ M] (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℝ M (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ M f).re := by
  classical
  let c := Module.Free.chooseBasis ℂ M
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower c), LinearMap.trace_eq_matrix_trace ℂ c]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Fintype.sum_prod_type, LinearMap.restrictScalars_apply, LinearMap.map_smul, map_smul, Finsupp.smul_apply,
    smul_eq_mul, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Fin.sum_univ_two]
  simp [Complex.re_sum, Finset.mul_sum, Finset.sum_add_distrib, two_mul]
end Formalism.L2.Pj.DatLin
