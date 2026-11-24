-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.basis_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:06.954415+00:00
-- url     : https://prove2.me/submissions/e7ba61d2-69d0-4ca6-8c93-3a47b66b3641

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {W : Type} [AddCommGroup W] [Module ℂ W]
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution {n : ℕ} (r : Fin n → ℂ) (i : Fin n) :
    (X - C (r i)) * Lagrange.basis univ r i =
      C (∏ j ∈ univ.erase i, (r i - r j)⁻¹) * ∏ j, (X - C (r j)) := by
  unfold Lagrange.basis Lagrange.basisDivisor
  rw [Finset.prod_mul_distrib, ← map_prod, ← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]
  ring
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
