-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.norm_u_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:32.525991+00:00
-- url     : https://prove2.me/submissions/26a851ba-0c8c-4b5d-91ac-08d5e9e2eea2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_UbTerms
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_NormUSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) (hη : 0 ≤ η) :
    ‖∑ i, ((η : ℂ) / w i) ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖ := by
  have e : ∑ i, ((η : ℂ) / w i) ^ j = (η : ℂ) ^ j * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, mul_one_div]
  rw [e, norm_mul, norm_pow]
  congr 2
  simpa using abs_of_nonneg hη
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
