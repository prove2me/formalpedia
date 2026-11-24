-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.exp_mulVec_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:47:59.757527+00:00
-- url     : https://prove2.me/submissions/40d410b6-7687-468f-a350-683064a17a0c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
set_option backward.isDefEq.respectTransparency false
open scoped Norms.Operator
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (h : Y *ᵥ v = 0) :
    NormedSpace.exp Y *ᵥ v = v := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h2 := hs.map (Matrix.mulVec.addMonoidHomLeft v)
    (Continuous.matrix_mulVec continuous_id continuous_const)
  have e : ((Matrix.mulVec.addMonoidHomLeft v) ∘ fun m : ℕ => ((m.factorial : ℂ)⁻¹) • Y ^ m) =
      fun m => if m = 0 then v else 0 := by
    funext m
    show (((m.factorial : ℂ)⁻¹) • Y ^ m) *ᵥ v = _
    rcases m with _ | m
    · simp
    · rw [Matrix.smul_mulVec, pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero]
      simp
  rw [e] at h2
  exact h2.unique (hasSum_ite_eq 0 v)
end Formalism.FourierDecayAlt.Q.EabGlW
