-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux7.powerMatch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:42:17.320954+00:00
-- url     : https://prove2.me/submissions/0c6dada2-4496-43b3-96f4-740518362ad3

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetTopConvergence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux7
namespace Formalism.FourierDecayAlt.P.Ux7
theorem _root_.solution : PowerMatch := by
  intro m M β t D V _ _ Φ hM ht
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  have hnt : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have key : ((‖t‖ ^ (m + 1))⁻¹ * ‖t‖ ^ ((m + 1) * (M' + 2 + m)) * ‖D / t ^ (m + 1)‖ ^ M' : ℝ) =
      ‖D‖ ^ M' * ‖t‖ ^ ((m + 1) ^ 2) := by
    rw [norm_div, norm_pow, div_pow]
    field_simp
    ring
  have hc : D / t ^ (m + 1) * t ^ (m + 1) = D := div_mul_cancel₀ D (pow_ne_zero _ ht)
  simp only [uD, aD, G.remainder, Nat.add_sub_cancel]
  rw [key, hc, smul_sub, smul_smul, Complex.ofReal_mul]
end Formalism.FourierDecayAlt.P.Ux7
