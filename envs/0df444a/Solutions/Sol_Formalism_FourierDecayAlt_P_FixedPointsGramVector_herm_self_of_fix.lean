-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FixedPointsGramVector.herm_self_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:22.052726+00:00
-- url     : https://prove2.me/submissions/b1af3fb7-2579-44d0-a75d-d9bb980186c2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FixedPointsGramVector
theorem _root_.solution (y : Fin (2 * r + k + 1) → ℂ) (hy : Hpk k r *ᵥ y = y) :
    herm (Hpk k r) y y = ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) := by
  unfold herm
  rw [hy]
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.normSq_eq_conj_mul_self]
  rfl
end Formalism.FourierDecayAlt.P.FixedPointsGramVector
