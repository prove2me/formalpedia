-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.map_smul_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:51.332368+00:00
-- url     : https://prove2.me/submissions/c2b4e405-11db-4a06-adaa-134b36116342

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_map_mulVec_volume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {n : ℕ} (c : ℂ) (hc : c ≠ 0) :
    (volume : Measure (Fin n → ℂ)).map (fun y => c • y) = ENNReal.ofReal ((‖c‖ ^ (2 * n))⁻¹) • volume := by
  have hA : (c • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0 := by simp [Matrix.det_smul, hc]
  have e : (fun y : Fin n → ℂ => c • y) = fun y => (c • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ y := by
    funext y; ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [e, map_mulVec_volume _ hA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow, ← pow_mul, mul_comm n 2]
end Formalism.FourierDecayAlt.P.B2x8
