-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:00.772868+00:00
-- url     : https://prove2.me/submissions/c4d37dc4-7d29-4b2f-b883-a1a5742873fb

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials
theorem _root_.solution {n : ℕ} (β : ℂ) {M : Fin n → ℤ} (hM : StrictAnti M) : SDec (shf β M) := by
  intro a b hab
  have h := hM hab
  refine ⟨(M a - M b - 1).toNat, ?_⟩
  have h1 : (((M a - M b - 1).toNat : ℤ) : ℂ) = ((M a - M b - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at h1
  rw [h1]
  simp only [shf]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
