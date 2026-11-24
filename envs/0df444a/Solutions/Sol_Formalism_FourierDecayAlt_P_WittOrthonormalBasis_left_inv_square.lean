-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WittOrthonormalBasis.left_inv_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:46.598904+00:00
-- url     : https://prove2.me/submissions/bcce605e-c0ff-42a0-b9dd-f91f2df9fbf7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WittOrthonormalBasis

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
open Formalism.FourierDecayAlt.P.WittOrthonormalBasis
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WittOrthonormalBasis
theorem _root_.solution {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (W : Matrix (Fin n) κ ℂ)
    (L : Matrix κ (Fin n) ℂ) (hcard : Fintype.card κ = n) (h : L * W = 1) : W * L = 1 := by
  exact (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hcard)).mp h
end Formalism.FourierDecayAlt.P.WittOrthonormalBasis
