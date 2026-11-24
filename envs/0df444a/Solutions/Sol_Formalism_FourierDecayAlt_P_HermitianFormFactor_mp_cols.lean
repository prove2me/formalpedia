-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.mp_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:40:58.24496+00:00
-- url     : https://prove2.me/submissions/e6565e6f-8345-49cd-888c-eee612e1fc3f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_mp_vec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (g : Matrix m m ℂ) (h : ‖g.det‖ = 1) :
    MeasurePreserving (fun (Y : Q → m → ℂ) j => g *ᵥ Y j) volume volume :=
  volume_preserving_pi (fun _ => mp_vec g h)
end Formalism.FourierDecayAlt.P.HermitianFormFactor
