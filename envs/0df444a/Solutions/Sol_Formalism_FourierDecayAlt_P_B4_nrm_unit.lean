-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.nrm_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:49:34.442197+00:00
-- url     : https://prove2.me/submissions/3802206b-d9d3-4f5f-b4bc-e3afed70a01c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_rsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma entry_le_lemma (A : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖A i j‖ ≤ ‖A‖ := by
  first
    | exact Matrix.norm_entry_le_entrywise_sup_norm A
    | exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {x : Bool × Mat k r} (hx : inLie k r x.2) : unitLie k r (nrm x).2 := by
  refine ⟨inLie_rsmul hx _, fun i j => ?_⟩
  simp only [nrm, Matrix.smul_apply, smul_eq_mul, norm_mul]
  rw [show ‖((‖x.2‖⁻¹ : ℝ) : ℂ)‖ = ‖x.2‖⁻¹ by simp]
  by_cases h0 : ‖x.2‖ = 0
  · rw [h0, _root_.inv_zero, zero_mul]
    exact zero_le_one
  · calc ‖x.2‖⁻¹ * ‖x.2 i j‖ ≤ ‖x.2‖⁻¹ * ‖x.2‖ :=
        mul_le_mul_of_nonneg_left (entry_le_lemma x.2 i j) (inv_nonneg.mpr (norm_nonneg _))
      _ = 1 := inv_mul_cancel₀ h0
end Formalism.FourierDecayAlt.P.B4
