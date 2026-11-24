-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.long_weyl_parametrisation_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:52.923799+00:00
-- url     : https://prove2.me/submissions/74ebc2f8-bfa5-4d7f-92c5-f3c4369f3af6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_long_weyl_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cf_hb_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cf_hb_ne

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
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (c₀ : ℂ) (hc : c₀ ≠ 0) (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) (h2 : p.2.2 ≠ 0) :
    w0 k r' c₀ *ᵥ Ψt k r' p = Ψt k r' (Tw k r' c₀ p) := by
  simp only [Ψt, Tw, long_weyl_three_block]
  have hh : hb k r' p.2.1 p.2.2 ≠ 0 := cf_hb_ne p.2.1 p.2.2 h2
  have hh' : (starRingEnd ℂ) (hb k r' p.2.1 p.2.2) ≠ 0 := by simpa using hh
  have hc' : (starRingEnd ℂ) c₀ ≠ 0 := by simpa using hc
  rw [cf_hb_neg]
  congr 1
  · simp only [map_div₀, map_mul, Complex.conj_conj]
    field_simp
  · ring
end Formalism.FourierDecayAlt.P.B2x8
