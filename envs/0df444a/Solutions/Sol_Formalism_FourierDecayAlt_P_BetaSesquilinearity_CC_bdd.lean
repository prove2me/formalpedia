-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CC_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:51.448056+00:00
-- url     : https://prove2.me/submissions/1125a6ff-47bd-417c-bbf6-55db4f385fd3

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one

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
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {A : ℝ} (hA : 0 ≤ A) {f : Mat k r → E} {c : ℝ} (hf : CCle A 0 f c) :
    ∀ g ∈ GV k r, ‖f g‖ ≤ c := by
  intro g hg
  have h1 := hf.2 [] [] (by simp) (by simp) (by simp) g hg
  have h2 : 1 ≤ gN g ^ A := Real.one_le_rpow (gN_ge_one hg) hA
  have h3 : dLR [] [] f g = f g := rfl
  rw [h3] at h1
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (norm_nonneg (f g))]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
