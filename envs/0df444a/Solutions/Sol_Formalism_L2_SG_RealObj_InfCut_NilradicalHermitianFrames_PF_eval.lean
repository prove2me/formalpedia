-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:35.458117+00:00
-- url     : https://prove2.me/submissions/e48ed82c-b735-4a5f-b55e-1edcfba6556f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_VolumeZeroFintype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
theorem _root_.solution {ι : Type*} (p : MvPolynomial ι ℂ) (y : ι → ℝ) :
    (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ)) p : (ι → ℝ) → ℂ) y =
      MvPolynomial.eval (fun i => (y i : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.aeval_C]
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X p i hp => simp only [map_mul, Pi.mul_apply, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]
end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
