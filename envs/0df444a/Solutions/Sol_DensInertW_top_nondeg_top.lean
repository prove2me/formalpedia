-- Prove2me | solution 1 for DensInertW.top_nondeg_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:15.174336+00:00
-- url     : https://prove2.me/submissions/9d6d298c-d92a-47ef-b25c-4e6d9f6e6167

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensExactInertOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution {L : Type} [Field L] {n : ℕ} (q : ℕ) (hq : 0 < q)
    (M : Matrix (Fin n) (Fin n) L) (hdet : IsUnit M.det) : NonDeg q M ⊤ := by
  intro w _ hw
  have h0 : Matrix.vecMul w M = 0 := by
    funext l0
    have h := hw (Pi.single l0 1) Submodule.mem_top
    simp only [hf, Pi.single_apply, ite_pow, one_pow, zero_pow hq.ne', mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    simpa [Matrix.vecMul, dotProduct] using h
  calc w = Matrix.vecMul w (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul w M) M⁻¹ := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [h0, Matrix.zero_vecMul]
end DensInertW
