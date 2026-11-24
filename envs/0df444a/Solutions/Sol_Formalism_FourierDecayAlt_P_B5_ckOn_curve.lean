-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.ckOn_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:19:42.592176+00:00
-- url     : https://prove2.me/submissions/3ab7bd5a-3a05-4535-a707-b5256e16581f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_contDiff

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution {f : Mat k r → E} (h : CkOn 1 (GV k r) f) {g X : Mat k r} (hg : g ∈ GV k r)
    (hX : inLie k r X) : ContDiff ℝ 1 (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  have hm := curve_mem hg hX t₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h _ hm
  have hcd : ContDiffAt ℝ 1 (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) t₀ :=
    (curve_contDiff g X).contDiffAt
  have hf'a : ContDiffAt ℝ 1 f' (g * NormedSpace.exp ((t₀ : ℂ) • X)) := hf'.contDiffAt (hU.mem_nhds hgU)
  have hcomp := hf'a.comp t₀ hcd
  apply hcomp.congr_of_eventuallyEq
  have hU' : ∀ᶠ t : ℝ in 𝓝 t₀, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hcd.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  filter_upwards [hU'] with t ht
  exact he _ ht (curve_mem hg hX t)
end Formalism.FourierDecayAlt.P.B5
