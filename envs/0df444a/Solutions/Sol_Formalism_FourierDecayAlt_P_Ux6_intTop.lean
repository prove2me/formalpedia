-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.intTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:50.565105+00:00
-- url     : https://prove2.me/submissions/72664cc5-93bf-4169-97e7-ea52f0a63551

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_intH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution : IntTop := by
  intro p s σ a ha
  have hq : ∀ D : ℕ, D ≤ 2 * (p + s) ^ 2 → (D : ℝ) < a := fun D hD =>
    lt_of_le_of_lt (by
      have : ((D : ℕ) : ℝ) ≤ ((2 * (p + s) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hD
      simpa using this) ha
  exact intH p s σ a (hq _ (by nlinarith [Nat.zero_le (p * s), Nat.zero_le (s * s), Nat.zero_le (p * p)])) (hq _ (by nlinarith [Nat.zero_le (p * s), Nat.zero_le (s * s), Nat.zero_le (p * p)]))
    (hq _ (by nlinarith [Nat.zero_le (p * s), Nat.zero_le (s * s), Nat.zero_le (p * p)]))
end Formalism.FourierDecayAlt.P.Ux6
