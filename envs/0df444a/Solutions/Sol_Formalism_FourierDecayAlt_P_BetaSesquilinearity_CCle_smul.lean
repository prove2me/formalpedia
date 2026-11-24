-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:43:58.02759+00:00
-- url     : https://prove2.me/submissions/f73c2401-9f2b-438c-a38b-521389889adc

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {A : ℝ} {m : ℕ} {F : Mat k r → E} {c : ℝ} (a : ℂ) (hF : CCle A m F c) :
    CCle A m (fun g => a • F g) (‖a‖ * c) := by
  obtain ⟨hc, hb⟩ := hF
  refine ⟨CkOn_smul a hc, fun u v hu hv hl g hg => ?_⟩
  have e : dLR u v (fun g => a • F g) g = a • dLR u v F g := by
    rw [dLR_eq, dLR_eq, Dw_smul]
  rw [e, norm_smul]
  calc gN g ^ A * (‖a‖ * ‖dLR u v F g‖) = ‖a‖ * (gN g ^ A * ‖dLR u v F g‖) := by ring
    _ ≤ ‖a‖ * c := mul_le_mul_of_nonneg_left (hb u v hu hv hl g hg) (norm_nonneg _)
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
