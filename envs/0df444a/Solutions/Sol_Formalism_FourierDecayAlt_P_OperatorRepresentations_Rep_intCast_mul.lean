-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.Rep.intCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:11.915796+00:00
-- url     : https://prove2.me/submissions/f1f9be1b-1557-49e3-8b04-e50ffe4de4a1

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
namespace Rep
theorem _root_.solution {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (n : ℤ) :
    Rep (((n : ℤ) : Module.End ℂ (SV k r i D E)) * X) (fun f x => (n : ℂ) • T f x) := by
  have e : ((n : ℤ) : Module.End ℂ (SV k r i D E)) * X = (n : ℂ) • X := by
    rw [← zsmul_eq_mul, Int.cast_smul_eq_zsmul]
  rw [e]
  exact hX.smul _
end Rep
end Formalism.FourierDecayAlt.P.OperatorRepresentations
