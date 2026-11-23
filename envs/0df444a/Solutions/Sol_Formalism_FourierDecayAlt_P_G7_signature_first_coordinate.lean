-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.signature_first_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:35.005797+00:00
-- url     : https://prove2.me/submissions/0386cd69-8acc-416a-9279-72bd02234ed5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_cornerSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {m : ℕ} (D t σ : ℂ) (ht : t ≠ 0) (ρ' : Fin m → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (B : Fin (m + 1) → ℂ) (hC : Cof X B t ≠ 0) :
    sig D t (Fin.cons (rho1 D σ ρ' X B t) ρ') X B = σ := by
  unfold sig
  rw [cornerSplit m X B _ ρ' t, rho1, mul_div_cancel₀ _ hC, div_eq_iff (pow_ne_zero _ ht)]
  ring
end Formalism.FourierDecayAlt.P.G7
