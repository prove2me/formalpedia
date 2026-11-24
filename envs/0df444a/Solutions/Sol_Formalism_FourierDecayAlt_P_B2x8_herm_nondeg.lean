-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.herm_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:54.269192+00:00
-- url     : https://prove2.me/submissions/4f417f96-065d-44f1-aea4-282e871d2091

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (h : ∀ x, herm (Hpk k r) x y = 0) : y = 0 := by
  have h1 : star y ᵥ* Hpk k r = 0 := by
    funext j
    have := h (Pi.single j 1)
    simp only [herm] at this
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    exact this
  have h2 : star y = 0 := by
    have := congrArg (fun v => v ᵥ* Hpk k r) h1
    simp only [Matrix.vecMul_vecMul, Hpk_sq, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    exact this
  simpa using congrArg star h2
end Formalism.FourierDecayAlt.P.B2x8
