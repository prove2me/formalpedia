-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:52:00.687817+00:00
-- url     : https://prove2.me/submissions/b21adfdb-7570-4004-9051-a99bccd65a35

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
theorem _root_.solution {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : StrictAnti fun a => (m a).re := by
  intro a b hab
  obtain ⟨N, hN⟩ := hm a b hab
  have h := congrArg Complex.re hN
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  show (m b).re < (m a).re
  linarith
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
