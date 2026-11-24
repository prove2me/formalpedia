-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.zs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:56:12.653062+00:00
-- url     : https://prove2.me/submissions/823eb8b4-6337-40c4-9dd3-4d0a3d106f02

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
variable {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → A)
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution (k : ℕ) (a : A) : ((-1 : ℤ) ^ k) • a = ((-1 : ℂ) ^ k) • a := by
  rw [← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
