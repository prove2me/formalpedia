-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.conj_inverse_map_inj_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:06:55.851513+00:00
-- url     : https://prove2.me/submissions/dd0d2caa-48b4-485a-ab44-1e2f63ad14a0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

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
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (l : ℂ) (hl : l ≠ 0) : Set.InjOn (fun c : ℂ => l / conj c) {(0 : ℂ)}ᶜ := by
  intro a ha b hb hab
  have ha' : conj a ≠ 0 := (map_ne_zero _).2 ha
  have hb' : conj b ≠ 0 := (map_ne_zero _).2 hb
  dsimp only at hab
  rw [div_eq_div_iff ha' hb'] at hab
  have := mul_left_cancel₀ hl hab
  exact ((starRingEnd ℂ).injective this).symm
end Formalism.FourierDecayAlt.P.B2x8
